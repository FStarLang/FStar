open Prims
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____4 = FStar_Options.print_real_names () in
    if uu____4
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let lid_to_string: FStar_Ident.lid -> Prims.string = fun l  -> sli l
let fv_to_string: FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let bv_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____15 =
      let uu____16 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____16 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____15
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____20 = FStar_Options.print_real_names () in
    if uu____20
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____25 =
      let uu____26 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____26 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____25
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
  | uu____105 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____118 -> failwith "get_lid"
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
let is_inr uu___198_165 =
  match uu___198_165 with
  | FStar_Util.Inl uu____168 -> false
  | FStar_Util.Inr uu____169 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___199_200  ->
          match uu___199_200 with
          | (uu____204,Some (FStar_Syntax_Syntax.Implicit uu____205)) ->
              false
          | uu____207 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____218 =
      let uu____219 = FStar_Syntax_Subst.compress e in
      uu____219.FStar_Syntax_Syntax.n in
    match uu____218 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives.fst args1 in
        let uu____265 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____265
        then
          let uu____274 =
            let uu____279 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____279 in
          (match uu____274 with
           | Some xs ->
               let uu____293 =
                 let uu____297 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____297 :: xs in
               Some uu____293
           | None  -> None)
        else None
    | uu____317 ->
        let uu____318 = is_lex_top e in if uu____318 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____354 = f hd1 in if uu____354 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____368 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____368
let infix_prim_op_to_string e =
  let uu____387 = get_lid e in find_lid uu____387 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____399 = get_lid e in find_lid uu____399 unary_prim_ops
let quant_to_string t =
  let uu____411 = get_lid t in find_lid uu____411 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____419) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____422 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____427) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____437 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____437
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___200_440  ->
    match uu___200_440 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____447 = db_to_string x in Prims.strcat "Tm_bvar: " uu____447
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____449 = nm_to_string x in Prims.strcat "Tm_name: " uu____449
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____451 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____451
    | FStar_Syntax_Syntax.Tm_uinst uu____452 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____457 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____458 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____459 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____474 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____482 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____487 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____497 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____512 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____530 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____538 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____549,m) ->
        let uu____587 = FStar_ST.read m in
        (match uu____587 with
         | None  -> "Tm_delayed"
         | Some uu____598 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____603 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____611 = FStar_Options.hide_uvar_nums () in
    if uu____611
    then "?"
    else
      (let uu____613 =
         let uu____614 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____614 FStar_Util.string_of_int in
       Prims.strcat "?" uu____613)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____618 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____619 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____618 uu____619
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____623 = FStar_Options.hide_uvar_nums () in
    if uu____623
    then "?"
    else
      (let uu____625 =
         let uu____626 =
           let uu____627 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____627 FStar_Util.string_of_int in
         let uu____628 =
           let uu____629 = version_to_string (snd u) in
           Prims.strcat ":" uu____629 in
         Prims.strcat uu____626 uu____628 in
       Prims.strcat "?" uu____625)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____641 = FStar_Syntax_Subst.compress_univ u in
      match uu____641 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____647 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____652 =
      let uu____653 = FStar_Options.ugly () in Prims.op_Negation uu____653 in
    if uu____652
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____657 = FStar_Syntax_Subst.compress_univ u in
       match uu____657 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____665 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____665
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____667 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____667 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____676 = univ_to_string u2 in
                let uu____677 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____676 uu____677)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____680 =
             let uu____681 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____681 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____680
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____689 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____689 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____697 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____697 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___201_703  ->
    match uu___201_703 with
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
        let uu____705 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____705
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____708 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____708 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____715 =
          let uu____716 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____716 in
        let uu____718 =
          let uu____719 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____719 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____715 uu____718
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____730 =
          let uu____731 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____731 in
        let uu____733 =
          let uu____734 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____734 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____730 uu____733
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____740 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____740
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
    | uu____747 ->
        let uu____749 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____749 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____759 ->
        let uu____761 = quals_to_string quals in Prims.strcat uu____761 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____809 =
      let uu____810 = FStar_Options.ugly () in Prims.op_Negation uu____810 in
    if uu____809
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____816 = FStar_Options.print_implicits () in
         if uu____816 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____818 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____839,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____866 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____882 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____890  ->
                                 match uu____890 with
                                 | (t1,uu____894) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____882
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____866 (FStar_String.concat "\\/") in
           let uu____897 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____897
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____909 = tag_of_term t in
           let uu____910 = sli m in
           let uu____911 = term_to_string t' in
           let uu____912 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____909 uu____910
             uu____911 uu____912
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____925 = tag_of_term t in
           let uu____926 = term_to_string t' in
           let uu____927 = sli m0 in
           let uu____928 = sli m1 in
           let uu____929 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____925
             uu____926 uu____927 uu____928 uu____929
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____938 = FStar_Range.string_of_range r in
           let uu____939 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____938
             uu____939
       | FStar_Syntax_Syntax.Tm_meta (t,uu____941) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____947 = db_to_string x3 in
           let uu____948 =
             let uu____949 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____949 in
           Prims.strcat uu____947 uu____948
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____953) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____972 = FStar_Options.print_universes () in
           if uu____972
           then
             let uu____973 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____973
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____987 = binders_to_string " -> " bs in
           let uu____988 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____987 uu____988
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1023 = binders_to_string " " bs in
                let uu____1024 = term_to_string t2 in
                let uu____1025 =
                  let uu____1026 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1026 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1023
                  uu____1024 uu____1025
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1039 = binders_to_string " " bs in
                let uu____1040 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1039 uu____1040 l.FStar_Ident.str
            | uu____1041 ->
                let uu____1048 = binders_to_string " " bs in
                let uu____1049 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1048 uu____1049)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1056 = bv_to_string xt in
           let uu____1057 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1060 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1056 uu____1057 uu____1060
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1079 = term_to_string t in
           let uu____1080 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1079 uu____1080
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1093 = lbs_to_string [] lbs in
           let uu____1094 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1093 uu____1094
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1142 =
                   let uu____1143 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1143
                     (FStar_Util.dflt "default") in
                 let uu____1146 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1142 uu____1146
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1162 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1162 in
           let uu____1163 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1163 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1190 = term_to_string head1 in
           let uu____1191 =
             let uu____1192 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1209  ->
                       match uu____1209 with
                       | (p,wopt,e) ->
                           let uu____1219 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1220 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1222 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1222 in
                           let uu____1223 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1219
                             uu____1220 uu____1223)) in
             FStar_Util.concat_l "\n\t|" uu____1192 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1190 uu____1191
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1230 = FStar_Options.print_universes () in
           if uu____1230
           then
             let uu____1231 = term_to_string t in
             let uu____1232 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1231 uu____1232
           else term_to_string t
       | uu____1234 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1236 =
      let uu____1237 = FStar_Options.ugly () in Prims.op_Negation uu____1237 in
    if uu____1236
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1251 = fv_to_string l in
           let uu____1252 =
             let uu____1253 =
               FStar_List.map
                 (fun uu____1257  ->
                    match uu____1257 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1253 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1251 uu____1252
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1266) ->
           let uu____1271 = FStar_Options.print_bound_var_types () in
           if uu____1271
           then
             let uu____1272 = bv_to_string x1 in
             let uu____1273 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1272 uu____1273
           else
             (let uu____1275 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1275)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1277 = FStar_Options.print_bound_var_types () in
           if uu____1277
           then
             let uu____1278 = bv_to_string x1 in
             let uu____1279 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1278 uu____1279
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1283 = FStar_Options.print_real_names () in
           if uu____1283
           then
             let uu____1284 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1284
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1296 = FStar_Options.print_universes () in
        if uu____1296
        then
          let uu____1300 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1306 =
                      let uu____1309 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1309 in
                    match uu____1306 with
                    | (us,td) ->
                        let uu____1312 =
                          let uu____1319 =
                            let uu____1320 = FStar_Syntax_Subst.compress td in
                            uu____1320.FStar_Syntax_Syntax.n in
                          match uu____1319 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1329,(t,uu____1331)::(d,uu____1333)::[])
                              -> (t, d)
                          | uu____1367 -> failwith "Impossibe" in
                        (match uu____1312 with
                         | (t,d) ->
                             let uu___208_1384 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___208_1384.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___208_1384.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1300)
        else lbs in
      let uu____1388 = quals_to_string' quals in
      let uu____1389 =
        let uu____1390 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1396 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1397 =
                    let uu____1398 = FStar_Options.print_universes () in
                    if uu____1398
                    then
                      let uu____1399 =
                        let uu____1400 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1400 ">" in
                      Prims.strcat "<" uu____1399
                    else "" in
                  let uu____1402 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1403 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1396 uu____1397
                    uu____1402 uu____1403)) in
        FStar_Util.concat_l "\n and " uu____1390 in
      FStar_Util.format3 "%slet %s %s" uu____1388
        (if fst lbs1 then "rec" else "") uu____1389
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1409 = FStar_Options.print_effect_args () in
    if uu____1409
    then
      let uu____1410 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1410
    else
      (let uu____1412 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1413 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1412 uu____1413)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___202_1415  ->
      match uu___202_1415 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1417 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1421 =
        let uu____1422 = FStar_Options.ugly () in
        Prims.op_Negation uu____1422 in
      if uu____1421
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1426 = b in
         match uu____1426 with
         | (a,imp) ->
             let uu____1429 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1429
             then
               let uu____1430 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1430
             else
               (let uu____1432 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1433 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1433) in
                if uu____1432
                then
                  let uu____1434 = nm_to_string a in
                  imp_to_string uu____1434 imp
                else
                  (let uu____1436 =
                     let uu____1437 = nm_to_string a in
                     let uu____1438 =
                       let uu____1439 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1439 in
                     Prims.strcat uu____1437 uu____1438 in
                   imp_to_string uu____1436 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1445 = FStar_Options.print_implicits () in
        if uu____1445 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1447 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1447 (FStar_String.concat sep)
      else
        (let uu____1452 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1452 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___203_1456  ->
    match uu___203_1456 with
    | (a,imp) ->
        let uu____1464 = term_to_string a in imp_to_string uu____1464 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1467 = FStar_Options.print_implicits () in
      if uu____1467 then args else filter_imp args in
    let uu____1471 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1471 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1479 =
      let uu____1480 = FStar_Options.ugly () in Prims.op_Negation uu____1480 in
    if uu____1479
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1492 =
             let uu____1493 = FStar_Syntax_Subst.compress t in
             uu____1493.FStar_Syntax_Syntax.n in
           (match uu____1492 with
            | FStar_Syntax_Syntax.Tm_type uu____1496 when
                let uu____1497 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1497 -> term_to_string t
            | uu____1498 ->
                (match uopt with
                 | Some u when FStar_Options.print_universes () ->
                     let uu____1500 = univ_to_string u in
                     let uu____1501 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1500 uu____1501
                 | uu____1502 ->
                     let uu____1504 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1504))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1513 =
             let uu____1514 = FStar_Syntax_Subst.compress t in
             uu____1514.FStar_Syntax_Syntax.n in
           (match uu____1513 with
            | FStar_Syntax_Syntax.Tm_type uu____1517 when
                let uu____1518 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1518 -> term_to_string t
            | uu____1519 ->
                (match uopt with
                 | Some u when FStar_Options.print_universes () ->
                     let uu____1521 = univ_to_string u in
                     let uu____1522 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1521 uu____1522
                 | uu____1523 ->
                     let uu____1525 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1525))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1528 = FStar_Options.print_effect_args () in
             if uu____1528
             then
               let uu____1529 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1530 =
                 let uu____1531 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1531 (FStar_String.concat ", ") in
               let uu____1535 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1536 =
                 let uu____1537 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1537 (FStar_String.concat ", ") in
               let uu____1549 =
                 let uu____1550 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1550 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1529
                 uu____1530 uu____1535 uu____1536 uu____1549
             else
               (let uu____1556 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___204_1558  ->
                           match uu___204_1558 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1559 -> false)))
                    &&
                    (let uu____1560 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1560) in
                if uu____1556
                then
                  let uu____1561 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1561
                else
                  (let uu____1563 =
                     ((let uu____1564 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1564) &&
                        (let uu____1565 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1565))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1563
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1567 =
                        (let uu____1568 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1568) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___205_1570  ->
                                   match uu___205_1570 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1571 -> false))) in
                      if uu____1567
                      then
                        let uu____1572 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1572
                      else
                        (let uu____1574 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1575 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1574 uu____1575)))) in
           let dec =
             let uu____1577 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___206_1581  ->
                       match uu___206_1581 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1586 =
                             let uu____1587 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1587 in
                           [uu____1586]
                       | uu____1588 -> [])) in
             FStar_All.pipe_right uu____1577 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1591 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1600 = FStar_Options.print_universes () in
    if uu____1600 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1605 =
      let uu____1606 = FStar_Options.ugly () in Prims.op_Negation uu____1606 in
    if uu____1605
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1610 = s in
       match uu____1610 with
       | (us,t) ->
           let uu____1615 =
             let uu____1616 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1616 in
           let uu____1617 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1615 uu____1617)
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
          let uu____1632 =
            let uu____1633 = FStar_Options.ugly () in
            Prims.op_Negation uu____1633 in
          if uu____1632
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1643 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1648 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1649 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1650 =
                           let uu____1651 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1651 in
                         let uu____1652 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1653 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1648
                           uu____1649 uu____1650 uu____1652 uu____1653)) in
               FStar_All.pipe_right uu____1643 (FStar_String.concat ",\n\t") in
             let uu____1655 =
               let uu____1657 =
                 let uu____1659 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1660 =
                   let uu____1662 =
                     let uu____1663 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1663 in
                   let uu____1664 =
                     let uu____1666 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1667 =
                       let uu____1669 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1670 =
                         let uu____1672 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1673 =
                           let uu____1675 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1676 =
                             let uu____1678 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1679 =
                               let uu____1681 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1682 =
                                 let uu____1684 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1685 =
                                   let uu____1687 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1688 =
                                     let uu____1690 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1691 =
                                       let uu____1693 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1694 =
                                         let uu____1696 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1697 =
                                           let uu____1699 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1700 =
                                             let uu____1702 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1703 =
                                               let uu____1705 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1706 =
                                                 let uu____1708 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1709 =
                                                   let uu____1711 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1711] in
                                                 uu____1708 :: uu____1709 in
                                               uu____1705 :: uu____1706 in
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
                   uu____1662 :: uu____1664 in
                 uu____1659 :: uu____1660 in
               (if for_free then "_for_free " else "") :: uu____1657 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1655)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1722 =
      let uu____1723 = FStar_Options.ugly () in Prims.op_Negation uu____1723 in
    if uu____1722
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1728 -> ""
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
           (lid,univs1,tps,k,uu____1737,uu____1738) ->
           let uu____1743 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1744 = binders_to_string " " tps in
           let uu____1745 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1743
             lid.FStar_Ident.str uu____1744 uu____1745
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1749,uu____1750,uu____1751) ->
           let uu____1754 = FStar_Options.print_universes () in
           if uu____1754
           then
             let uu____1755 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1755 with
              | (univs2,t1) ->
                  let uu____1760 = univ_names_to_string univs2 in
                  let uu____1761 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1760
                    lid.FStar_Ident.str uu____1761)
           else
             (let uu____1763 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1763)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1767 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1767 with
            | (univs2,t1) ->
                let uu____1772 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1773 =
                  let uu____1774 = FStar_Options.print_universes () in
                  if uu____1774
                  then
                    let uu____1775 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1775
                  else "" in
                let uu____1777 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1772
                  lid.FStar_Ident.str uu____1773 uu____1777)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____1779,f) ->
           let uu____1781 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1781
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1783,uu____1784) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1790 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1790
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1792) ->
           let uu____1797 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1797 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1809) -> lift_wp
             | (uu____1813,Some lift) -> lift in
           let uu____1818 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1818 with
            | (us,t) ->
                let uu____1825 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1826 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1827 = univ_names_to_string us in
                let uu____1828 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1825
                  uu____1826 uu____1827 uu____1828)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1836 = FStar_Options.print_universes () in
           if uu____1836
           then
             let uu____1837 =
               let uu____1840 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1840 in
             (match uu____1837 with
              | (univs2,t) ->
                  let uu____1851 =
                    let uu____1859 =
                      let uu____1860 = FStar_Syntax_Subst.compress t in
                      uu____1860.FStar_Syntax_Syntax.n in
                    match uu____1859 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1887 -> failwith "impossible" in
                  (match uu____1851 with
                   | (tps1,c1) ->
                       let uu____1907 = sli l in
                       let uu____1908 = univ_names_to_string univs2 in
                       let uu____1909 = binders_to_string " " tps1 in
                       let uu____1910 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1907
                         uu____1908 uu____1909 uu____1910))
           else
             (let uu____1912 = sli l in
              let uu____1913 = binders_to_string " " tps in
              let uu____1914 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1912 uu____1913
                uu____1914))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1921 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1921 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1925,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1927;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1929;
                       FStar_Syntax_Syntax.lbdef = uu____1930;_}::[]),uu____1931,uu____1932)
        ->
        let uu____1948 = lbname_to_string lb in
        let uu____1949 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1948 uu____1949
    | uu____1950 ->
        let uu____1951 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1951 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1960 = sli m.FStar_Syntax_Syntax.name in
    let uu____1961 =
      let uu____1962 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1962 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1960 uu____1961
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___207_1967  ->
    match uu___207_1967 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1970 = FStar_Util.string_of_int i in
        let uu____1971 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1970 uu____1971
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1974 = bv_to_string x in
        let uu____1975 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1974 uu____1975
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1982 = bv_to_string x in
        let uu____1983 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1982 uu____1983
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1986 = FStar_Util.string_of_int i in
        let uu____1987 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1986 uu____1987
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1990 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1990
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1994 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1994 (FStar_String.concat "; ")
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
       (let uu____2044 = f x in
        FStar_Util.string_builder_append strb uu____2044);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2048 = f x1 in
             FStar_Util.string_builder_append strb uu____2048)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2077 = f x in
        FStar_Util.string_builder_append strb uu____2077);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2081 = f x1 in
             FStar_Util.string_builder_append strb uu____2081)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)