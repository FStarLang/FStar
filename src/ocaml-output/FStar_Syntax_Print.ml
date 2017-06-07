open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___209_3  ->
    match uu___209_3 with
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
    let uu____27 =
      let uu____28 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____28 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____27
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____32 = FStar_Options.print_real_names () in
    if uu____32
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____37 =
      let uu____38 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____38 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____37
let infix_prim_ops: (FStar_Ident.lident* Prims.string) Prims.list =
  [(FStar_Syntax_Const.op_Addition, "+");
  (FStar_Syntax_Const.op_Subtraction, "-");
  (FStar_Syntax_Const.op_Multiply, "*");
  (FStar_Syntax_Const.op_Division, "/");
  (FStar_Syntax_Const.op_Eq, "=");
  (FStar_Syntax_Const.op_ColonEq, ":=");
  (FStar_Syntax_Const.op_notEq, "<>");
  (FStar_Syntax_Const.op_And, "&&");
  (FStar_Syntax_Const.op_Or, "||");
  (FStar_Syntax_Const.op_LTE, "<=");
  (FStar_Syntax_Const.op_GTE, ">=");
  (FStar_Syntax_Const.op_LT, "<");
  (FStar_Syntax_Const.op_GT, ">");
  (FStar_Syntax_Const.op_Modulus, "mod");
  (FStar_Syntax_Const.and_lid, "/\\");
  (FStar_Syntax_Const.or_lid, "\\/");
  (FStar_Syntax_Const.imp_lid, "==>");
  (FStar_Syntax_Const.iff_lid, "<==>");
  (FStar_Syntax_Const.precedes_lid, "<<");
  (FStar_Syntax_Const.eq2_lid, "==");
  (FStar_Syntax_Const.eq3_lid, "===")]
let unary_prim_ops: (FStar_Ident.lident* Prims.string) Prims.list =
  [(FStar_Syntax_Const.op_Negation, "not");
  (FStar_Syntax_Const.op_Minus, "-");
  (FStar_Syntax_Const.not_lid, "~")]
let is_prim_op ps f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_All.pipe_right ps
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
  | uu____117 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____134 -> failwith "get_lid"
let is_infix_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (fst (FStar_List.split infix_prim_ops)) e
let is_unary_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (fst (FStar_List.split unary_prim_ops)) e
let quants: (FStar_Ident.lident* Prims.string) Prims.list =
  [(FStar_Syntax_Const.forall_lid, "forall");
  (FStar_Syntax_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term
let is_b2t: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.b2t_lid] t
let is_quant: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op (fst (FStar_List.split quants)) t
let is_ite: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.ite_lid] t
let is_lex_cons: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lexcons_lid] f
let is_lex_top: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lextop_lid] f
let is_inr uu___210_181 =
  match uu___210_181 with
  | FStar_Util.Inl uu____184 -> false
  | FStar_Util.Inr uu____185 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___211_216  ->
          match uu___211_216 with
          | (uu____220,Some (FStar_Syntax_Syntax.Implicit uu____221)) ->
              false
          | uu____223 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____234 =
      let uu____235 = FStar_Syntax_Subst.compress e in
      uu____235.FStar_Syntax_Syntax.n in
    match uu____234 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives.fst args1 in
        let uu____281 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____281
        then
          let uu____290 =
            let uu____295 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____295 in
          (match uu____290 with
           | Some xs ->
               let uu____309 =
                 let uu____313 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____313 :: xs in
               Some uu____309
           | None  -> None)
        else None
    | uu____333 ->
        let uu____334 = is_lex_top e in if uu____334 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____370 = f hd1 in if uu____370 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____384 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____384
let infix_prim_op_to_string e =
  let uu____403 = get_lid e in find_lid uu____403 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____415 = get_lid e in find_lid uu____415 unary_prim_ops
let quant_to_string t =
  let uu____427 = get_lid t in find_lid uu____427 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____435) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____438 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____443) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____453 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____453
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___212_456  ->
    match uu___212_456 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____467 = db_to_string x in Prims.strcat "Tm_bvar: " uu____467
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____469 = nm_to_string x in Prims.strcat "Tm_name: " uu____469
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____471 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____471
    | FStar_Syntax_Syntax.Tm_uinst uu____476 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____481 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____482 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____483 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____498 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____506 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____511 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____521 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____537 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____555 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____563 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____572,m) ->
        let uu____610 = FStar_ST.read m in
        (match uu____610 with
         | None  -> "Tm_delayed"
         | Some uu____621 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____626 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____634 = FStar_Options.hide_uvar_nums () in
    if uu____634
    then "?"
    else
      (let uu____636 =
         let uu____637 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____637 FStar_Util.string_of_int in
       Prims.strcat "?" uu____636)
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____641 = FStar_Options.hide_uvar_nums () in
    if uu____641
    then "?"
    else
      (let uu____643 =
         let uu____644 = FStar_Syntax_Unionfind.univ_uvar_id u in
         FStar_All.pipe_right uu____644 FStar_Util.string_of_int in
       Prims.strcat "?" uu____643)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____654 = FStar_Syntax_Subst.compress_univ u in
      match uu____654 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____660 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____665 =
      let uu____666 = FStar_Options.ugly () in Prims.op_Negation uu____666 in
    if uu____665
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____670 = FStar_Syntax_Subst.compress_univ u in
       match uu____670 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____676 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____676
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____678 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____678 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____687 = univ_to_string u2 in
                let uu____688 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____687 uu____688)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____691 =
             let uu____692 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____692 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____691
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____700 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____700 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____708 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____708 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___213_714  ->
    match uu___213_714 with
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
        let uu____716 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____716
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____719 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____719 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____726 =
          let uu____727 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____727 in
        let uu____729 =
          let uu____730 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____730 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____726 uu____729
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____741 =
          let uu____742 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____742 in
        let uu____744 =
          let uu____745 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____745 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____741 uu____744
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____751 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____751
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
    | uu____758 ->
        let uu____760 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____760 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____770 ->
        let uu____772 = quals_to_string quals in Prims.strcat uu____772 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____820 =
      let uu____821 = FStar_Options.ugly () in Prims.op_Negation uu____821 in
    if uu____820
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____827 = FStar_Options.print_implicits () in
         if uu____827 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____829 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____850,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____877 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____893 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____901  ->
                                 match uu____901 with
                                 | (t1,uu____905) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____893
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____877 (FStar_String.concat "\\/") in
           let uu____908 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____908
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____920 = tag_of_term t in
           let uu____921 = sli m in
           let uu____922 = term_to_string t' in
           let uu____923 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____920 uu____921
             uu____922 uu____923
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____936 = tag_of_term t in
           let uu____937 = term_to_string t' in
           let uu____938 = sli m0 in
           let uu____939 = sli m1 in
           let uu____940 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____936
             uu____937 uu____938 uu____939 uu____940
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____949 = FStar_Range.string_of_range r in
           let uu____950 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____949
             uu____950
       | FStar_Syntax_Syntax.Tm_meta (t,uu____952) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____961) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____976 = FStar_Options.print_universes () in
           if uu____976
           then
             let uu____977 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____977
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____991 = binders_to_string " -> " bs in
           let uu____992 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____991 uu____992
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1027 = binders_to_string " " bs in
                let uu____1028 = term_to_string t2 in
                let uu____1029 =
                  let uu____1030 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1030 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1027
                  uu____1028 uu____1029
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1043 = binders_to_string " " bs in
                let uu____1044 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1043 uu____1044 l.FStar_Ident.str
            | uu____1045 ->
                let uu____1052 = binders_to_string " " bs in
                let uu____1053 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1052 uu____1053)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1060 = bv_to_string xt in
           let uu____1061 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1064 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1060 uu____1061 uu____1064
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1083 = term_to_string t in
           let uu____1084 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1083 uu____1084
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1097 = lbs_to_string [] lbs in
           let uu____1098 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1097 uu____1098
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1146 =
                   let uu____1147 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1147
                     (FStar_Util.dflt "default") in
                 let uu____1150 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1146 uu____1150
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1166 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1166 in
           let uu____1167 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1167 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1196 = term_to_string head1 in
           let uu____1197 =
             let uu____1198 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1216  ->
                       match uu____1216 with
                       | (p,wopt,e) ->
                           let uu____1226 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1227 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1229 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1229 in
                           let uu____1230 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1226
                             uu____1227 uu____1230)) in
             FStar_Util.concat_l "\n\t|" uu____1198 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1196 uu____1197
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1237 = FStar_Options.print_universes () in
           if uu____1237
           then
             let uu____1238 = term_to_string t in
             let uu____1239 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1238 uu____1239
           else term_to_string t
       | uu____1241 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1243 =
      let uu____1244 = FStar_Options.ugly () in Prims.op_Negation uu____1244 in
    if uu____1243
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1260 = fv_to_string l in
           let uu____1261 =
             let uu____1262 =
               FStar_List.map
                 (fun uu____1266  ->
                    match uu____1266 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1262 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1260 uu____1261
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1275) ->
           let uu____1280 = FStar_Options.print_bound_var_types () in
           if uu____1280
           then
             let uu____1281 = bv_to_string x1 in
             let uu____1282 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1281 uu____1282
           else
             (let uu____1284 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1284)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1286 = FStar_Options.print_bound_var_types () in
           if uu____1286
           then
             let uu____1287 = bv_to_string x1 in
             let uu____1288 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1287 uu____1288
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1292 = FStar_Options.print_real_names () in
           if uu____1292
           then
             let uu____1293 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1293
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1305 = FStar_Options.print_universes () in
        if uu____1305
        then
          let uu____1309 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1315 =
                      let uu____1318 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1318 in
                    match uu____1315 with
                    | (us,td) ->
                        let uu____1321 =
                          let uu____1328 =
                            let uu____1329 = FStar_Syntax_Subst.compress td in
                            uu____1329.FStar_Syntax_Syntax.n in
                          match uu____1328 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1338,(t,uu____1340)::(d,uu____1342)::[])
                              -> (t, d)
                          | uu____1376 -> failwith "Impossibe" in
                        (match uu____1321 with
                         | (t,d) ->
                             let uu___220_1393 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___220_1393.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___220_1393.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1309)
        else lbs in
      let uu____1397 = quals_to_string' quals in
      let uu____1398 =
        let uu____1399 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1405 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1406 =
                    let uu____1407 = FStar_Options.print_universes () in
                    if uu____1407
                    then
                      let uu____1408 =
                        let uu____1409 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1409 ">" in
                      Prims.strcat "<" uu____1408
                    else "" in
                  let uu____1411 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1412 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1405 uu____1406
                    uu____1411 uu____1412)) in
        FStar_Util.concat_l "\n and " uu____1399 in
      FStar_Util.format3 "%slet %s %s" uu____1397
        (if fst lbs1 then "rec" else "") uu____1398
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1418 = FStar_Options.print_effect_args () in
    if uu____1418
    then
      let uu____1419 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1419
    else
      (let uu____1421 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1422 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1421 uu____1422)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___214_1424  ->
      match uu___214_1424 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1426 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1430 =
        let uu____1431 = FStar_Options.ugly () in
        Prims.op_Negation uu____1431 in
      if uu____1430
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1435 = b in
         match uu____1435 with
         | (a,imp) ->
             let uu____1438 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1438
             then
               let uu____1439 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1439
             else
               (let uu____1441 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1442 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1442) in
                if uu____1441
                then
                  let uu____1443 = nm_to_string a in
                  imp_to_string uu____1443 imp
                else
                  (let uu____1445 =
                     let uu____1446 = nm_to_string a in
                     let uu____1447 =
                       let uu____1448 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1448 in
                     Prims.strcat uu____1446 uu____1447 in
                   imp_to_string uu____1445 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1454 = FStar_Options.print_implicits () in
        if uu____1454 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1456 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1456 (FStar_String.concat sep)
      else
        (let uu____1461 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1461 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___215_1465  ->
    match uu___215_1465 with
    | (a,imp) ->
        let uu____1473 = term_to_string a in imp_to_string uu____1473 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1476 = FStar_Options.print_implicits () in
      if uu____1476 then args else filter_imp args in
    let uu____1480 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1480 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1488 =
      let uu____1489 = FStar_Options.ugly () in Prims.op_Negation uu____1489 in
    if uu____1488
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1494) ->
           let uu____1501 =
             let uu____1502 = FStar_Syntax_Subst.compress t in
             uu____1502.FStar_Syntax_Syntax.n in
           (match uu____1501 with
            | FStar_Syntax_Syntax.Tm_type uu____1505 when
                let uu____1506 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1506 -> term_to_string t
            | uu____1507 ->
                let uu____1508 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1508)
       | FStar_Syntax_Syntax.GTotal (t,uu____1510) ->
           let uu____1517 =
             let uu____1518 = FStar_Syntax_Subst.compress t in
             uu____1518.FStar_Syntax_Syntax.n in
           (match uu____1517 with
            | FStar_Syntax_Syntax.Tm_type uu____1521 when
                let uu____1522 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1522 -> term_to_string t
            | uu____1523 ->
                let uu____1524 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1524)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1527 = FStar_Options.print_effect_args () in
             if uu____1527
             then
               let uu____1528 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1529 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1530 =
                 let uu____1531 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1531 (FStar_String.concat ", ") in
               let uu____1543 =
                 let uu____1544 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1544 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1528
                 uu____1529 uu____1530 uu____1543
             else
               (let uu____1550 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___216_1552  ->
                           match uu___216_1552 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1553 -> false)))
                    &&
                    (let uu____1554 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1554) in
                if uu____1550
                then
                  let uu____1555 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1555
                else
                  (let uu____1557 =
                     ((let uu____1558 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1558) &&
                        (let uu____1559 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1559))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1557
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1561 =
                        (let uu____1562 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1562) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___217_1564  ->
                                   match uu___217_1564 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1565 -> false))) in
                      if uu____1561
                      then
                        let uu____1566 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1566
                      else
                        (let uu____1568 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1569 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1568 uu____1569)))) in
           let dec =
             let uu____1571 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___218_1575  ->
                       match uu___218_1575 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1580 =
                             let uu____1581 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1581 in
                           [uu____1580]
                       | uu____1582 -> [])) in
             FStar_All.pipe_right uu____1571 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1585 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1594 = FStar_Options.print_universes () in
    if uu____1594 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1599 =
      let uu____1600 = FStar_Options.ugly () in Prims.op_Negation uu____1600 in
    if uu____1599
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1604 = s in
       match uu____1604 with
       | (us,t) ->
           let uu____1609 =
             let uu____1610 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1610 in
           let uu____1611 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1609 uu____1611)
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
          let uu____1626 =
            let uu____1627 = FStar_Options.ugly () in
            Prims.op_Negation uu____1627 in
          if uu____1626
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1637 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1642 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1643 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1644 =
                           let uu____1645 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1645 in
                         let uu____1646 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1647 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1642
                           uu____1643 uu____1644 uu____1646 uu____1647)) in
               FStar_All.pipe_right uu____1637 (FStar_String.concat ",\n\t") in
             let uu____1649 =
               let uu____1651 =
                 let uu____1653 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1654 =
                   let uu____1656 =
                     let uu____1657 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1657 in
                   let uu____1658 =
                     let uu____1660 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1661 =
                       let uu____1663 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1664 =
                         let uu____1666 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1667 =
                           let uu____1669 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1670 =
                             let uu____1672 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1673 =
                               let uu____1675 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1676 =
                                 let uu____1678 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1679 =
                                   let uu____1681 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1682 =
                                     let uu____1684 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1685 =
                                       let uu____1687 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1688 =
                                         let uu____1690 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1691 =
                                           let uu____1693 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1694 =
                                             let uu____1696 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1697 =
                                               let uu____1699 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1700 =
                                                 let uu____1702 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1703 =
                                                   let uu____1705 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1705] in
                                                 uu____1702 :: uu____1703 in
                                               uu____1699 :: uu____1700 in
                                             uu____1696 :: uu____1697 in
                                           uu____1693 :: uu____1694 in
                                         uu____1690 :: uu____1691 in
                                       uu____1687 :: uu____1688 in
                                     uu____1684 :: uu____1685 in
                                   uu____1681 :: uu____1682 in
                                 uu____1678 :: uu____1679 in
                               uu____1675 :: uu____1676 in
                             uu____1672 :: uu____1673 in
                           uu____1669 :: uu____1670 in
                         uu____1666 :: uu____1667 in
                       uu____1663 :: uu____1664 in
                     uu____1660 :: uu____1661 in
                   uu____1656 :: uu____1658 in
                 uu____1653 :: uu____1654 in
               (if for_free then "_for_free " else "") :: uu____1651 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1649)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1716 =
      let uu____1717 = FStar_Options.ugly () in Prims.op_Negation uu____1717 in
    if uu____1716
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1722 -> ""
    else
      (match x.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
           "#light \"off\""
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           (None )) -> "#reset-options"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           (Some s)) -> FStar_Util.format1 "#reset-options \"%s\"" s
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
           FStar_Util.format1 "#set-options \"%s\"" s
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (lid,univs1,tps,k,uu____1731,uu____1732) ->
           let uu____1737 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1738 = binders_to_string " " tps in
           let uu____1739 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1737
             lid.FStar_Ident.str uu____1738 uu____1739
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1743,uu____1744,uu____1745) ->
           let uu____1748 = FStar_Options.print_universes () in
           if uu____1748
           then
             let uu____1749 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1749 with
              | (univs2,t1) ->
                  let uu____1754 = univ_names_to_string univs2 in
                  let uu____1755 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1754
                    lid.FStar_Ident.str uu____1755)
           else
             (let uu____1757 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1757)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1761 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1761 with
            | (univs2,t1) ->
                let uu____1766 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1767 =
                  let uu____1768 = FStar_Options.print_universes () in
                  if uu____1768
                  then
                    let uu____1769 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1769
                  else "" in
                let uu____1771 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1766
                  lid.FStar_Ident.str uu____1767 uu____1771)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1774 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1774
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1776,uu____1777) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1783 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1783
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1785) ->
           let uu____1790 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1790 (FStar_String.concat "\n")
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
             | (None ,None ) -> failwith "impossible"
             | (Some lift_wp,uu____1802) -> lift_wp
             | (uu____1806,Some lift) -> lift in
           let uu____1811 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1811 with
            | (us,t) ->
                let uu____1818 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1819 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1820 = univ_names_to_string us in
                let uu____1821 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1818
                  uu____1819 uu____1820 uu____1821)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1829 = FStar_Options.print_universes () in
           if uu____1829
           then
             let uu____1830 =
               let uu____1833 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1833 in
             (match uu____1830 with
              | (univs2,t) ->
                  let uu____1844 =
                    let uu____1852 =
                      let uu____1853 = FStar_Syntax_Subst.compress t in
                      uu____1853.FStar_Syntax_Syntax.n in
                    match uu____1852 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1880 -> failwith "impossible" in
                  (match uu____1844 with
                   | (tps1,c1) ->
                       let uu____1900 = sli l in
                       let uu____1901 = univ_names_to_string univs2 in
                       let uu____1902 = binders_to_string " " tps1 in
                       let uu____1903 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1900
                         uu____1901 uu____1902 uu____1903))
           else
             (let uu____1905 = sli l in
              let uu____1906 = binders_to_string " " tps in
              let uu____1907 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1905 uu____1906
                uu____1907))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1914 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1914 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1918,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1920;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1922;
                       FStar_Syntax_Syntax.lbdef = uu____1923;_}::[]),uu____1924,uu____1925)
        ->
        let uu____1941 = lbname_to_string lb in
        let uu____1942 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1941 uu____1942
    | uu____1943 ->
        let uu____1944 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1944 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1953 = sli m.FStar_Syntax_Syntax.name in
    let uu____1954 =
      let uu____1955 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1955 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1953 uu____1954
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___219_1960  ->
    match uu___219_1960 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1963 = FStar_Util.string_of_int i in
        let uu____1964 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1963 uu____1964
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1967 = bv_to_string x in
        let uu____1968 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1967 uu____1968
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1975 = bv_to_string x in
        let uu____1976 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1975 uu____1976
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1979 = FStar_Util.string_of_int i in
        let uu____1980 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1979 uu____1980
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1983 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1983
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1987 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1987 (FStar_String.concat "; ")
let abs_ascription_to_string:
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either option ->
    Prims.string
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder () in
    (match ascription with
     | None  -> FStar_Util.string_builder_append strb "None"
     | Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb
            (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name))
     | Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)));
    FStar_Util.string_of_string_builder strb
let list_to_string f elts =
  match elts with
  | [] -> "[]"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "[";
       (let uu____2037 = f x in
        FStar_Util.string_builder_append strb uu____2037);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2041 = f x1 in
             FStar_Util.string_builder_append strb uu____2041)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2070 = f x in
        FStar_Util.string_builder_append strb uu____2070);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2074 = f x1 in
             FStar_Util.string_builder_append strb uu____2074)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)