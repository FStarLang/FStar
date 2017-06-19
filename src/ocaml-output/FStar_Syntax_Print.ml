open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___210_3  ->
    match uu___210_3 with
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
let is_inr uu___211_181 =
  match uu___211_181 with
  | FStar_Util.Inl uu____184 -> false
  | FStar_Util.Inr uu____185 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___212_216  ->
          match uu___212_216 with
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
  fun uu___213_456  ->
    match uu___213_456 with
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
    | FStar_Syntax_Syntax.Tm_arrow uu____493 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____501 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____506 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____516 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____532 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____550 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____558 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____567,m) ->
        let uu____593 = FStar_ST.read m in
        (match uu____593 with
         | None  -> "Tm_delayed"
         | Some uu____604 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____609 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____617 = FStar_Options.hide_uvar_nums () in
    if uu____617
    then "?"
    else
      (let uu____619 =
         let uu____620 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____620 FStar_Util.string_of_int in
       Prims.strcat "?" uu____619)
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____624 = FStar_Options.hide_uvar_nums () in
    if uu____624
    then "?"
    else
      (let uu____626 =
         let uu____627 = FStar_Syntax_Unionfind.univ_uvar_id u in
         FStar_All.pipe_right uu____627 FStar_Util.string_of_int in
       Prims.strcat "?" uu____626)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____637 = FStar_Syntax_Subst.compress_univ u in
      match uu____637 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____643 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____648 =
      let uu____649 = FStar_Options.ugly () in Prims.op_Negation uu____649 in
    if uu____648
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____653 = FStar_Syntax_Subst.compress_univ u in
       match uu____653 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____659 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____659
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____661 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____661 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____670 = univ_to_string u2 in
                let uu____671 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____670 uu____671)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____674 =
             let uu____675 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____675 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____674
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____683 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____683 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____691 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____691 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___214_697  ->
    match uu___214_697 with
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
        let uu____699 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____699
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____702 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____702 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____709 =
          let uu____710 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____710 in
        let uu____712 =
          let uu____713 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____713 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____709 uu____712
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____724 =
          let uu____725 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____725 in
        let uu____727 =
          let uu____728 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____728 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____724 uu____727
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____734 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____734
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
    | uu____741 ->
        let uu____743 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____743 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____753 ->
        let uu____755 = quals_to_string quals in Prims.strcat uu____755 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____803 =
      let uu____804 = FStar_Options.ugly () in Prims.op_Negation uu____804 in
    if uu____803
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____810 = FStar_Options.print_implicits () in
         if uu____810 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____812 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____827,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____854 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____870 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____878  ->
                                 match uu____878 with
                                 | (t1,uu____882) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____870
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____854 (FStar_String.concat "\\/") in
           let uu____885 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____885
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____897 = tag_of_term t in
           let uu____898 = sli m in
           let uu____899 = term_to_string t' in
           let uu____900 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____897 uu____898
             uu____899 uu____900
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____913 = tag_of_term t in
           let uu____914 = term_to_string t' in
           let uu____915 = sli m0 in
           let uu____916 = sli m1 in
           let uu____917 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____913
             uu____914 uu____915 uu____916 uu____917
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____926 = FStar_Range.string_of_range r in
           let uu____927 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____926
             uu____927
       | FStar_Syntax_Syntax.Tm_meta (t,uu____929) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____938) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____953 = FStar_Options.print_universes () in
           if uu____953
           then
             let uu____954 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____954
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____968 = binders_to_string " -> " bs in
           let uu____969 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____968 uu____969
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some rc when FStar_Options.print_implicits () ->
                let uu____986 = binders_to_string " " bs in
                let uu____987 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____986 uu____987
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
            | uu____988 ->
                let uu____990 = binders_to_string " " bs in
                let uu____991 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____990 uu____991)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____998 = bv_to_string xt in
           let uu____999 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1002 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____998 uu____999 uu____1002
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1021 = term_to_string t in
           let uu____1022 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1021 uu____1022
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1035 = lbs_to_string [] lbs in
           let uu____1036 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1035 uu____1036
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1084 =
                   let uu____1085 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1085
                     (FStar_Util.dflt "default") in
                 let uu____1088 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1084 uu____1088
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1104 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1104 in
           let uu____1105 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1105 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1134 = term_to_string head1 in
           let uu____1135 =
             let uu____1136 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1154  ->
                       match uu____1154 with
                       | (p,wopt,e) ->
                           let uu____1164 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1165 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1167 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1167 in
                           let uu____1168 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1164
                             uu____1165 uu____1168)) in
             FStar_Util.concat_l "\n\t|" uu____1136 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1134 uu____1135
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1175 = FStar_Options.print_universes () in
           if uu____1175
           then
             let uu____1176 = term_to_string t in
             let uu____1177 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1176 uu____1177
           else term_to_string t
       | uu____1179 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1181 =
      let uu____1182 = FStar_Options.ugly () in Prims.op_Negation uu____1182 in
    if uu____1181
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1198 = fv_to_string l in
           let uu____1199 =
             let uu____1200 =
               FStar_List.map
                 (fun uu____1204  ->
                    match uu____1204 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1200 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1198 uu____1199
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1213) ->
           let uu____1218 = FStar_Options.print_bound_var_types () in
           if uu____1218
           then
             let uu____1219 = bv_to_string x1 in
             let uu____1220 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1219 uu____1220
           else
             (let uu____1222 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1222)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1224 = FStar_Options.print_bound_var_types () in
           if uu____1224
           then
             let uu____1225 = bv_to_string x1 in
             let uu____1226 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1225 uu____1226
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1230 = FStar_Options.print_real_names () in
           if uu____1230
           then
             let uu____1231 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1231
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1243 = FStar_Options.print_universes () in
        if uu____1243
        then
          let uu____1247 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1253 =
                      let uu____1256 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1256 in
                    match uu____1253 with
                    | (us,td) ->
                        let uu____1259 =
                          let uu____1266 =
                            let uu____1267 = FStar_Syntax_Subst.compress td in
                            uu____1267.FStar_Syntax_Syntax.n in
                          match uu____1266 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1276,(t,uu____1278)::(d,uu____1280)::[])
                              -> (t, d)
                          | uu____1314 -> failwith "Impossibe" in
                        (match uu____1259 with
                         | (t,d) ->
                             let uu___221_1331 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___221_1331.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___221_1331.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1247)
        else lbs in
      let uu____1335 = quals_to_string' quals in
      let uu____1336 =
        let uu____1337 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1343 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1344 =
                    let uu____1345 = FStar_Options.print_universes () in
                    if uu____1345
                    then
                      let uu____1346 =
                        let uu____1347 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1347 ">" in
                      Prims.strcat "<" uu____1346
                    else "" in
                  let uu____1349 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1350 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1343 uu____1344
                    uu____1349 uu____1350)) in
        FStar_Util.concat_l "\n and " uu____1337 in
      FStar_Util.format3 "%slet %s %s" uu____1335
        (if fst lbs1 then "rec" else "") uu____1336
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1356 = FStar_Options.print_effect_args () in
    if uu____1356
    then
      let uu____1357 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1357
    else
      (let uu____1359 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1360 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1359 uu____1360)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___215_1362  ->
      match uu___215_1362 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1364 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1368 =
        let uu____1369 = FStar_Options.ugly () in
        Prims.op_Negation uu____1369 in
      if uu____1368
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1373 = b in
         match uu____1373 with
         | (a,imp) ->
             let uu____1376 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1376
             then
               let uu____1377 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1377
             else
               (let uu____1379 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1380 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1380) in
                if uu____1379
                then
                  let uu____1381 = nm_to_string a in
                  imp_to_string uu____1381 imp
                else
                  (let uu____1383 =
                     let uu____1384 = nm_to_string a in
                     let uu____1385 =
                       let uu____1386 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1386 in
                     Prims.strcat uu____1384 uu____1385 in
                   imp_to_string uu____1383 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1392 = FStar_Options.print_implicits () in
        if uu____1392 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1394 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1394 (FStar_String.concat sep)
      else
        (let uu____1399 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1399 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___216_1403  ->
    match uu___216_1403 with
    | (a,imp) ->
        let uu____1411 = term_to_string a in imp_to_string uu____1411 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1414 = FStar_Options.print_implicits () in
      if uu____1414 then args else filter_imp args in
    let uu____1418 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1418 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1426 =
      let uu____1427 = FStar_Options.ugly () in Prims.op_Negation uu____1427 in
    if uu____1426
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1432) ->
           let uu____1439 =
             let uu____1440 = FStar_Syntax_Subst.compress t in
             uu____1440.FStar_Syntax_Syntax.n in
           (match uu____1439 with
            | FStar_Syntax_Syntax.Tm_type uu____1443 when
                let uu____1444 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1444 -> term_to_string t
            | uu____1445 ->
                let uu____1446 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1446)
       | FStar_Syntax_Syntax.GTotal (t,uu____1448) ->
           let uu____1455 =
             let uu____1456 = FStar_Syntax_Subst.compress t in
             uu____1456.FStar_Syntax_Syntax.n in
           (match uu____1455 with
            | FStar_Syntax_Syntax.Tm_type uu____1459 when
                let uu____1460 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1460 -> term_to_string t
            | uu____1461 ->
                let uu____1462 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1462)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1465 = FStar_Options.print_effect_args () in
             if uu____1465
             then
               let uu____1466 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1467 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1468 =
                 let uu____1469 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1469 (FStar_String.concat ", ") in
               let uu____1481 =
                 let uu____1482 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1482 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1466
                 uu____1467 uu____1468 uu____1481
             else
               (let uu____1488 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___217_1490  ->
                           match uu___217_1490 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1491 -> false)))
                    &&
                    (let uu____1492 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1492) in
                if uu____1488
                then
                  let uu____1493 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1493
                else
                  (let uu____1495 =
                     ((let uu____1496 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1496) &&
                        (let uu____1497 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1497))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1495
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1499 =
                        (let uu____1500 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1500) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___218_1502  ->
                                   match uu___218_1502 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1503 -> false))) in
                      if uu____1499
                      then
                        let uu____1504 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1504
                      else
                        (let uu____1506 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1507 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1506 uu____1507)))) in
           let dec =
             let uu____1509 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___219_1513  ->
                       match uu___219_1513 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1518 =
                             let uu____1519 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1519 in
                           [uu____1518]
                       | uu____1520 -> [])) in
             FStar_All.pipe_right uu____1509 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1523 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1532 = FStar_Options.print_universes () in
    if uu____1532 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1537 =
      let uu____1538 = FStar_Options.ugly () in Prims.op_Negation uu____1538 in
    if uu____1537
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1542 = s in
       match uu____1542 with
       | (us,t) ->
           let uu____1547 =
             let uu____1548 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1548 in
           let uu____1549 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1547 uu____1549)
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
          let uu____1564 =
            let uu____1565 = FStar_Options.ugly () in
            Prims.op_Negation uu____1565 in
          if uu____1564
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1575 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1580 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1581 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1582 =
                           let uu____1583 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1583 in
                         let uu____1584 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1585 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1580
                           uu____1581 uu____1582 uu____1584 uu____1585)) in
               FStar_All.pipe_right uu____1575 (FStar_String.concat ",\n\t") in
             let uu____1587 =
               let uu____1589 =
                 let uu____1591 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1592 =
                   let uu____1594 =
                     let uu____1595 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1595 in
                   let uu____1596 =
                     let uu____1598 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1599 =
                       let uu____1601 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1602 =
                         let uu____1604 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1605 =
                           let uu____1607 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1608 =
                             let uu____1610 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1611 =
                               let uu____1613 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1614 =
                                 let uu____1616 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1617 =
                                   let uu____1619 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1620 =
                                     let uu____1622 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1623 =
                                       let uu____1625 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1626 =
                                         let uu____1628 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1629 =
                                           let uu____1631 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1632 =
                                             let uu____1634 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1635 =
                                               let uu____1637 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1638 =
                                                 let uu____1640 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1641 =
                                                   let uu____1643 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1643] in
                                                 uu____1640 :: uu____1641 in
                                               uu____1637 :: uu____1638 in
                                             uu____1634 :: uu____1635 in
                                           uu____1631 :: uu____1632 in
                                         uu____1628 :: uu____1629 in
                                       uu____1625 :: uu____1626 in
                                     uu____1622 :: uu____1623 in
                                   uu____1619 :: uu____1620 in
                                 uu____1616 :: uu____1617 in
                               uu____1613 :: uu____1614 in
                             uu____1610 :: uu____1611 in
                           uu____1607 :: uu____1608 in
                         uu____1604 :: uu____1605 in
                       uu____1601 :: uu____1602 in
                     uu____1598 :: uu____1599 in
                   uu____1594 :: uu____1596 in
                 uu____1591 :: uu____1592 in
               (if for_free then "_for_free " else "") :: uu____1589 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1587)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1654 =
      let uu____1655 = FStar_Options.ugly () in Prims.op_Negation uu____1655 in
    if uu____1654
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1660 -> ""
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
           (lid,univs1,tps,k,uu____1669,uu____1670) ->
           let uu____1675 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1676 = binders_to_string " " tps in
           let uu____1677 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1675
             lid.FStar_Ident.str uu____1676 uu____1677
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1681,uu____1682,uu____1683) ->
           let uu____1686 = FStar_Options.print_universes () in
           if uu____1686
           then
             let uu____1687 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1687 with
              | (univs2,t1) ->
                  let uu____1692 = univ_names_to_string univs2 in
                  let uu____1693 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1692
                    lid.FStar_Ident.str uu____1693)
           else
             (let uu____1695 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1695)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1699 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1699 with
            | (univs2,t1) ->
                let uu____1704 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1705 =
                  let uu____1706 = FStar_Options.print_universes () in
                  if uu____1706
                  then
                    let uu____1707 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1707
                  else "" in
                let uu____1709 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1704
                  lid.FStar_Ident.str uu____1705 uu____1709)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1712 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1712
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1714,uu____1715) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1721 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1721
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1723) ->
           let uu____1728 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1728 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1740) -> lift_wp
             | (uu____1744,Some lift) -> lift in
           let uu____1749 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1749 with
            | (us,t) ->
                let uu____1756 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1757 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1758 = univ_names_to_string us in
                let uu____1759 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1756
                  uu____1757 uu____1758 uu____1759)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1767 = FStar_Options.print_universes () in
           if uu____1767
           then
             let uu____1768 =
               let uu____1771 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1771 in
             (match uu____1768 with
              | (univs2,t) ->
                  let uu____1782 =
                    let uu____1790 =
                      let uu____1791 = FStar_Syntax_Subst.compress t in
                      uu____1791.FStar_Syntax_Syntax.n in
                    match uu____1790 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1818 -> failwith "impossible" in
                  (match uu____1782 with
                   | (tps1,c1) ->
                       let uu____1838 = sli l in
                       let uu____1839 = univ_names_to_string univs2 in
                       let uu____1840 = binders_to_string " " tps1 in
                       let uu____1841 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1838
                         uu____1839 uu____1840 uu____1841))
           else
             (let uu____1843 = sli l in
              let uu____1844 = binders_to_string " " tps in
              let uu____1845 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1843 uu____1844
                uu____1845))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1852 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1852 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1856,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1858;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1860;
                       FStar_Syntax_Syntax.lbdef = uu____1861;_}::[]),uu____1862,uu____1863)
        ->
        let uu____1879 = lbname_to_string lb in
        let uu____1880 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1879 uu____1880
    | uu____1881 ->
        let uu____1882 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1882 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1891 = sli m.FStar_Syntax_Syntax.name in
    let uu____1892 =
      let uu____1893 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1893 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1891 uu____1892
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___220_1898  ->
    match uu___220_1898 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1901 = FStar_Util.string_of_int i in
        let uu____1902 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1901 uu____1902
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1905 = bv_to_string x in
        let uu____1906 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1905 uu____1906
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1913 = bv_to_string x in
        let uu____1914 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1913 uu____1914
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1917 = FStar_Util.string_of_int i in
        let uu____1918 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1917 uu____1918
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1921 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1921
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1925 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1925 (FStar_String.concat "; ")
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
       (let uu____1975 = f x in
        FStar_Util.string_builder_append strb uu____1975);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____1979 = f x1 in
             FStar_Util.string_builder_append strb uu____1979)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2008 = f x in
        FStar_Util.string_builder_append strb uu____2008);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2012 = f x1 in
             FStar_Util.string_builder_append strb uu____2012)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)