open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___204_4  ->
    match uu___204_4 with
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
let is_inr uu___205_195 =
  match uu___205_195 with
  | FStar_Util.Inl uu____198 -> false
  | FStar_Util.Inr uu____199 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___206_235  ->
          match uu___206_235 with
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
      let uu____396 = f hd1 in if uu____396 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____412 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____412
let infix_prim_op_to_string e =
  let uu____434 = get_lid e in find_lid uu____434 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____448 = get_lid e in find_lid uu____448 unary_prim_ops
let quant_to_string t =
  let uu____462 = get_lid t in find_lid uu____462 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____471) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____474 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____479) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____489 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____489
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___207_493  ->
    match uu___207_493 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____501 = db_to_string x in Prims.strcat "Tm_bvar: " uu____501
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____503 = nm_to_string x in Prims.strcat "Tm_name: " uu____503
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____505 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____505
    | FStar_Syntax_Syntax.Tm_uinst uu____506 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____511 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____512 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____513 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____523 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____531 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____536 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____546 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____561 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____579 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____587 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____598,m) ->
        let uu____624 = FStar_ST.read m in
        (match uu____624 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____635 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____640 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____649 = FStar_Options.hide_uvar_nums () in
    if uu____649
    then "?"
    else
      (let uu____651 =
         let uu____652 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____652 FStar_Util.string_of_int in
       Prims.strcat "?" uu____651)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____657 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____658 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____657 uu____658
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____663 = FStar_Options.hide_uvar_nums () in
    if uu____663
    then "?"
    else
      (let uu____665 =
         let uu____666 =
           let uu____667 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____667 FStar_Util.string_of_int in
         let uu____668 =
           let uu____669 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____669 in
         Prims.strcat uu____666 uu____668 in
       Prims.strcat "?" uu____665)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____683 = FStar_Syntax_Subst.compress_univ u in
      match uu____683 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____689 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____695 =
      let uu____696 = FStar_Options.ugly () in Prims.op_Negation uu____696 in
    if uu____695
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____700 = FStar_Syntax_Subst.compress_univ u in
       match uu____700 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____708 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____708
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____710 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____710 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____719 = univ_to_string u2 in
                let uu____720 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____719 uu____720)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____723 =
             let uu____724 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____724 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____723
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____733 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____733 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____742 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____742 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___208_750  ->
    match uu___208_750 with
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
        let uu____752 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____752
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____755 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____755 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____762 =
          let uu____763 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____763 in
        let uu____765 =
          let uu____766 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____766 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____762 uu____765
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____777 =
          let uu____778 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____778 in
        let uu____780 =
          let uu____781 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____781 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____777 uu____780
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____787 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____787
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
    | uu____795 ->
        let uu____797 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____797 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____808 ->
        let uu____810 = quals_to_string quals in Prims.strcat uu____810 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____858 =
      let uu____859 = FStar_Options.ugly () in Prims.op_Negation uu____859 in
    if uu____858
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____865 = FStar_Options.print_implicits () in
         if uu____865 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____867 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____882,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____909 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____927 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____938  ->
                                 match uu____938 with
                                 | (t1,uu____942) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____927
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____909 (FStar_String.concat "\\/") in
           let uu____945 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____945
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____957 = tag_of_term t in
           let uu____958 = sli m in
           let uu____959 = term_to_string t' in
           let uu____960 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____957 uu____958
             uu____959 uu____960
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____973 = tag_of_term t in
           let uu____974 = term_to_string t' in
           let uu____975 = sli m0 in
           let uu____976 = sli m1 in
           let uu____977 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____973
             uu____974 uu____975 uu____976 uu____977
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____979,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____993 = FStar_Range.string_of_range r in
           let uu____994 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____993
             uu____994
       | FStar_Syntax_Syntax.Tm_meta (t,uu____996) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1002 = db_to_string x3 in
           let uu____1003 =
             let uu____1004 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1004 in
           Prims.strcat uu____1002 uu____1003
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1008) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1027 = FStar_Options.print_universes () in
           if uu____1027
           then
             let uu____1028 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1028
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1042 = binders_to_string " -> " bs in
           let uu____1043 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1042 uu____1043
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1060 = binders_to_string " " bs in
                let uu____1061 = term_to_string t2 in
                let uu____1062 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1066 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1066) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1060 uu____1061
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1062
            | uu____1069 ->
                let uu____1071 = binders_to_string " " bs in
                let uu____1072 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1071 uu____1072)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1079 = bv_to_string xt in
           let uu____1080 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1083 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1079 uu____1080 uu____1083
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1102 = term_to_string t in
           let uu____1103 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1102 uu____1103
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1116 = lbs_to_string [] lbs in
           let uu____1117 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1116 uu____1117
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1165 =
                   let uu____1166 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1166
                     (FStar_Util.dflt "default") in
                 let uu____1169 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1165 uu____1169
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1185 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1185 in
           let uu____1186 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1186 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1213 = term_to_string head1 in
           let uu____1214 =
             let uu____1215 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1239  ->
                       match uu____1239 with
                       | (p,wopt,e) ->
                           let uu____1249 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1250 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1252 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1252 in
                           let uu____1253 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1249
                             uu____1250 uu____1253)) in
             FStar_Util.concat_l "\n\t|" uu____1215 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1213 uu____1214
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1260 = FStar_Options.print_universes () in
           if uu____1260
           then
             let uu____1261 = term_to_string t in
             let uu____1262 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1261 uu____1262
           else term_to_string t
       | uu____1264 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1266 =
      let uu____1267 = FStar_Options.ugly () in Prims.op_Negation uu____1267 in
    if uu____1266
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1281 = fv_to_string l in
           let uu____1282 =
             let uu____1283 =
               FStar_List.map
                 (fun uu____1291  ->
                    match uu____1291 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1283 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1281 uu____1282
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1300) ->
           let uu____1305 = FStar_Options.print_bound_var_types () in
           if uu____1305
           then
             let uu____1306 = bv_to_string x1 in
             let uu____1307 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1306 uu____1307
           else
             (let uu____1309 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1309)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1311 = FStar_Options.print_bound_var_types () in
           if uu____1311
           then
             let uu____1312 = bv_to_string x1 in
             let uu____1313 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1312 uu____1313
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1317 = FStar_Options.print_real_names () in
           if uu____1317
           then
             let uu____1318 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1318
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1330 = FStar_Options.print_universes () in
        if uu____1330
        then
          let uu____1334 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1348 =
                      let uu____1351 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1351 in
                    match uu____1348 with
                    | (us,td) ->
                        let uu____1354 =
                          let uu____1361 =
                            let uu____1362 = FStar_Syntax_Subst.compress td in
                            uu____1362.FStar_Syntax_Syntax.n in
                          match uu____1361 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1371,(t,uu____1373)::(d,uu____1375)::[])
                              -> (t, d)
                          | uu____1409 -> failwith "Impossibe" in
                        (match uu____1354 with
                         | (t,d) ->
                             let uu___215_1426 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___215_1426.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___215_1426.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1334)
        else lbs in
      let uu____1430 = quals_to_string' quals in
      let uu____1431 =
        let uu____1432 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1443 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1444 =
                    let uu____1445 = FStar_Options.print_universes () in
                    if uu____1445
                    then
                      let uu____1446 =
                        let uu____1447 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1447 ">" in
                      Prims.strcat "<" uu____1446
                    else "" in
                  let uu____1449 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1450 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1443 uu____1444
                    uu____1449 uu____1450)) in
        FStar_Util.concat_l "\n and " uu____1432 in
      FStar_Util.format3 "%slet %s %s" uu____1430
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1431
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1456 = FStar_Options.print_effect_args () in
    if uu____1456
    then
      let uu____1457 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1457
    else
      (let uu____1459 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1460 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1459 uu____1460)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___209_1462  ->
      match uu___209_1462 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1464 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1468 =
        let uu____1469 = FStar_Options.ugly () in
        Prims.op_Negation uu____1469 in
      if uu____1468
      then
        let uu____1470 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1470 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1475 = b in
         match uu____1475 with
         | (a,imp) ->
             let uu____1478 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1478
             then
               let uu____1479 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1479
             else
               (let uu____1481 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1483 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1483) in
                if uu____1481
                then
                  let uu____1484 = nm_to_string a in
                  imp_to_string uu____1484 imp
                else
                  (let uu____1486 =
                     let uu____1487 = nm_to_string a in
                     let uu____1488 =
                       let uu____1489 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1489 in
                     Prims.strcat uu____1487 uu____1488 in
                   imp_to_string uu____1486 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1495 = FStar_Options.print_implicits () in
        if uu____1495 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1497 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1497 (FStar_String.concat sep)
      else
        (let uu____1502 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1502 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___210_1506  ->
    match uu___210_1506 with
    | (a,imp) ->
        let uu____1514 = term_to_string a in imp_to_string uu____1514 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1517 = FStar_Options.print_implicits () in
      if uu____1517 then args else filter_imp args in
    let uu____1521 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1521 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1529 =
      let uu____1530 = FStar_Options.ugly () in Prims.op_Negation uu____1530 in
    if uu____1529
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1542 =
             let uu____1543 = FStar_Syntax_Subst.compress t in
             uu____1543.FStar_Syntax_Syntax.n in
           (match uu____1542 with
            | FStar_Syntax_Syntax.Tm_type uu____1546 when
                let uu____1547 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1547 -> term_to_string t
            | uu____1548 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1550 = univ_to_string u in
                     let uu____1551 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1550 uu____1551
                 | uu____1552 ->
                     let uu____1554 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1554))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1563 =
             let uu____1564 = FStar_Syntax_Subst.compress t in
             uu____1564.FStar_Syntax_Syntax.n in
           (match uu____1563 with
            | FStar_Syntax_Syntax.Tm_type uu____1567 when
                let uu____1568 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1568 -> term_to_string t
            | uu____1569 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1571 = univ_to_string u in
                     let uu____1572 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1571 uu____1572
                 | uu____1573 ->
                     let uu____1575 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1575))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1578 = FStar_Options.print_effect_args () in
             if uu____1578
             then
               let uu____1579 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1580 =
                 let uu____1581 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1581 (FStar_String.concat ", ") in
               let uu____1585 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1586 =
                 let uu____1587 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1587 (FStar_String.concat ", ") in
               let uu____1599 =
                 let uu____1600 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1600 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1579
                 uu____1580 uu____1585 uu____1586 uu____1599
             else
               (let uu____1606 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___211_1609  ->
                           match uu___211_1609 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1610 -> false)))
                    &&
                    (let uu____1612 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1612) in
                if uu____1606
                then
                  let uu____1613 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1613
                else
                  (let uu____1615 =
                     ((let uu____1618 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1618) &&
                        (let uu____1620 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1620))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1615
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1622 =
                        (let uu____1625 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1625) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___212_1628  ->
                                   match uu___212_1628 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1629 -> false))) in
                      if uu____1622
                      then
                        let uu____1630 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1630
                      else
                        (let uu____1632 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1633 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1632 uu____1633)))) in
           let dec =
             let uu____1635 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___213_1642  ->
                       match uu___213_1642 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1647 =
                             let uu____1648 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1648 in
                           [uu____1647]
                       | uu____1649 -> [])) in
             FStar_All.pipe_right uu____1635 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1652 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1662 = FStar_Options.print_universes () in
    if uu____1662 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1668 =
      let uu____1669 = FStar_Options.ugly () in Prims.op_Negation uu____1669 in
    if uu____1668
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1673 = s in
       match uu____1673 with
       | (us,t) ->
           let uu____1678 =
             let uu____1679 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1679 in
           let uu____1680 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1678 uu____1680)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____1685 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____1686 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____1687 =
      let uu____1688 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____1688 in
    let uu____1689 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____1690 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____1685 uu____1686 uu____1687
      uu____1689 uu____1690
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
          let uu____1709 =
            let uu____1710 = FStar_Options.ugly () in
            Prims.op_Negation uu____1710 in
          if uu____1709
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1720 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____1720 (FStar_String.concat ",\n\t") in
             let uu____1725 =
               let uu____1727 =
                 let uu____1729 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1730 =
                   let uu____1732 =
                     let uu____1733 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1733 in
                   let uu____1734 =
                     let uu____1736 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1737 =
                       let uu____1739 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1740 =
                         let uu____1742 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1743 =
                           let uu____1745 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1746 =
                             let uu____1748 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1749 =
                               let uu____1751 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1752 =
                                 let uu____1754 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1755 =
                                   let uu____1757 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1758 =
                                     let uu____1760 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1761 =
                                       let uu____1763 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1764 =
                                         let uu____1766 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1767 =
                                           let uu____1769 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1770 =
                                             let uu____1772 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1773 =
                                               let uu____1775 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1776 =
                                                 let uu____1778 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1779 =
                                                   let uu____1781 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1781] in
                                                 uu____1778 :: uu____1779 in
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
                   uu____1732 :: uu____1734 in
                 uu____1729 :: uu____1730 in
               (if for_free then "_for_free " else "") :: uu____1727 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1725)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1795 =
      let uu____1796 = FStar_Options.ugly () in Prims.op_Negation uu____1796 in
    if uu____1795
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1801 -> ""
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
           (lid,univs1,tps,k,uu____1810,uu____1811) ->
           let uu____1816 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1817 = binders_to_string " " tps in
           let uu____1818 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1816
             lid.FStar_Ident.str uu____1817 uu____1818
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1822,uu____1823,uu____1824) ->
           let uu____1827 = FStar_Options.print_universes () in
           if uu____1827
           then
             let uu____1828 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1828 with
              | (univs2,t1) ->
                  let uu____1833 = univ_names_to_string univs2 in
                  let uu____1834 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1833
                    lid.FStar_Ident.str uu____1834)
           else
             (let uu____1836 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1836)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1840 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1840 with
            | (univs2,t1) ->
                let uu____1845 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1846 =
                  let uu____1847 = FStar_Options.print_universes () in
                  if uu____1847
                  then
                    let uu____1848 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1848
                  else "" in
                let uu____1850 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1845
                  lid.FStar_Ident.str uu____1846 uu____1850)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____1852,f) ->
           let uu____1854 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1854
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1856) ->
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
                       FStar_Syntax_Syntax.lbdef = uu____1999;_}::[]),uu____2000)
        ->
        let uu____2014 = lbname_to_string lb in
        let uu____2015 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2014 uu____2015
    | uu____2016 ->
        let uu____2017 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2017 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2028 = sli m.FStar_Syntax_Syntax.name in
    let uu____2029 =
      let uu____2030 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2030 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2028 uu____2029
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___214_2036  ->
    match uu___214_2036 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2039 = FStar_Util.string_of_int i in
        let uu____2040 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2039 uu____2040
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2043 = bv_to_string x in
        let uu____2044 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2043 uu____2044
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2051 = bv_to_string x in
        let uu____2052 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2051 uu____2052
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2055 = FStar_Util.string_of_int i in
        let uu____2056 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2055 uu____2056
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2059 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2059
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2064 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2064 (FStar_String.concat "; ")
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
       (let uu____2118 = f x in
        FStar_Util.string_builder_append strb uu____2118);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2125 = f x1 in
             FStar_Util.string_builder_append strb uu____2125)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2157 = f x in
        FStar_Util.string_builder_append strb uu____2157);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2164 = f x1 in
             FStar_Util.string_builder_append strb uu____2164)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)