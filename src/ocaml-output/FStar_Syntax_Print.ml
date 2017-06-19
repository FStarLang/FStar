open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___209_4  ->
    match uu___209_4 with
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
    let uu____32 =
      let uu____33 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____33 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____32
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____38 = FStar_Options.print_real_names () in
    if uu____38
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____44 =
      let uu____45 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____45 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____44
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
  | uu____127 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____146 -> failwith "get_lid"
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
let is_inr uu___210_203 =
  match uu___210_203 with
  | FStar_Util.Inl uu____206 -> false
  | FStar_Util.Inr uu____207 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___211_240  ->
          match uu___211_240 with
          | (uu____244,Some (FStar_Syntax_Syntax.Implicit uu____245)) ->
              false
          | uu____247 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____259 =
      let uu____260 = FStar_Syntax_Subst.compress e in
      uu____260.FStar_Syntax_Syntax.n in
    match uu____259 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives.fst args1 in
        let uu____306 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____306
        then
          let uu____317 =
            let uu____322 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____322 in
          (match uu____317 with
           | Some xs ->
               let uu____336 =
                 let uu____340 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____340 :: xs in
               Some uu____336
           | None  -> None)
        else None
    | uu____360 ->
        let uu____361 = is_lex_top e in if uu____361 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____400 = f hd1 in if uu____400 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____416 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____416
let infix_prim_op_to_string e =
  let uu____437 = get_lid e in find_lid uu____437 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____451 = get_lid e in find_lid uu____451 unary_prim_ops
let quant_to_string t =
  let uu____465 = get_lid t in find_lid uu____465 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____474) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____477 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____482) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____492 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____492
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___212_496  ->
    match uu___212_496 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____508 = db_to_string x in Prims.strcat "Tm_bvar: " uu____508
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____510 = nm_to_string x in Prims.strcat "Tm_name: " uu____510
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____512 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____512
    | FStar_Syntax_Syntax.Tm_uinst uu____517 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____522 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____523 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____524 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____539 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____547 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____552 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____562 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____578 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____596 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____604 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____613,m) ->
        let uu____651 = FStar_ST.read m in
        (match uu____651 with
         | None  -> "Tm_delayed"
         | Some uu____662 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____667 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____676 = FStar_Options.hide_uvar_nums () in
    if uu____676
    then "?"
    else
      (let uu____678 =
         let uu____679 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____679 FStar_Util.string_of_int in
       Prims.strcat "?" uu____678)
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____684 = FStar_Options.hide_uvar_nums () in
    if uu____684
    then "?"
    else
      (let uu____686 =
         let uu____687 = FStar_Syntax_Unionfind.univ_uvar_id u in
         FStar_All.pipe_right uu____687 FStar_Util.string_of_int in
       Prims.strcat "?" uu____686)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____699 = FStar_Syntax_Subst.compress_univ u in
      match uu____699 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____705 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____711 =
      let uu____712 = FStar_Options.ugly () in Prims.op_Negation uu____712 in
    if uu____711
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____716 = FStar_Syntax_Subst.compress_univ u in
       match uu____716 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____722 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____722
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____724 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____724 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____733 = univ_to_string u2 in
                let uu____734 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____733 uu____734)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____737 =
             let uu____738 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____738 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____737
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____747 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____747 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____756 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____756 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___213_763  ->
    match uu___213_763 with
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
        let uu____765 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____765
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____768 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____768 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____775 =
          let uu____776 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____776 in
        let uu____778 =
          let uu____779 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____779 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____775 uu____778
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____790 =
          let uu____791 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____791 in
        let uu____793 =
          let uu____794 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____794 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____790 uu____793
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____800 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____800
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
    | uu____808 ->
        let uu____810 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____810 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____821 ->
        let uu____823 = quals_to_string quals in Prims.strcat uu____823 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____871 =
      let uu____872 = FStar_Options.ugly () in Prims.op_Negation uu____872 in
    if uu____871
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____878 = FStar_Options.print_implicits () in
         if uu____878 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____880 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____901,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____928 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____944 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____952  ->
                                 match uu____952 with
                                 | (t1,uu____956) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____944
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____928 (FStar_String.concat "\\/") in
           let uu____959 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____959
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____971 = tag_of_term t in
           let uu____972 = sli m in
           let uu____973 = term_to_string t' in
           let uu____974 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____971 uu____972
             uu____973 uu____974
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____987 = tag_of_term t in
           let uu____988 = term_to_string t' in
           let uu____989 = sli m0 in
           let uu____990 = sli m1 in
           let uu____991 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____987
             uu____988 uu____989 uu____990 uu____991
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1000 = FStar_Range.string_of_range r in
           let uu____1001 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1000
             uu____1001
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1003) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1012) -> uvar_to_string u
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
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1078 = binders_to_string " " bs in
                let uu____1079 = term_to_string t2 in
                let uu____1080 =
                  let uu____1081 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1081 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1078
                  uu____1079 uu____1080
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1094 = binders_to_string " " bs in
                let uu____1095 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1094 uu____1095 l.FStar_Ident.str
            | uu____1096 ->
                let uu____1103 = binders_to_string " " bs in
                let uu____1104 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1103 uu____1104)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1111 = bv_to_string xt in
           let uu____1112 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1115 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1111 uu____1112 uu____1115
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1134 = term_to_string t in
           let uu____1135 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1134 uu____1135
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1148 = lbs_to_string [] lbs in
           let uu____1149 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1148 uu____1149
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1197 =
                   let uu____1198 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1198
                     (FStar_Util.dflt "default") in
                 let uu____1201 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1197 uu____1201
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1217 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1217 in
           let uu____1218 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1218 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1247 = term_to_string head1 in
           let uu____1248 =
             let uu____1249 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1267  ->
                       match uu____1267 with
                       | (p,wopt,e) ->
                           let uu____1277 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1278 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1280 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1280 in
                           let uu____1281 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1277
                             uu____1278 uu____1281)) in
             FStar_Util.concat_l "\n\t|" uu____1249 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1247 uu____1248
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1288 = FStar_Options.print_universes () in
           if uu____1288
           then
             let uu____1289 = term_to_string t in
             let uu____1290 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1289 uu____1290
           else term_to_string t
       | uu____1292 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1294 =
      let uu____1295 = FStar_Options.ugly () in Prims.op_Negation uu____1295 in
    if uu____1294
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1311 = fv_to_string l in
           let uu____1312 =
             let uu____1313 =
               FStar_List.map
                 (fun uu____1317  ->
                    match uu____1317 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1313 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1311 uu____1312
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1326) ->
           let uu____1331 = FStar_Options.print_bound_var_types () in
           if uu____1331
           then
             let uu____1332 = bv_to_string x1 in
             let uu____1333 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1332 uu____1333
           else
             (let uu____1335 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1335)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1337 = FStar_Options.print_bound_var_types () in
           if uu____1337
           then
             let uu____1338 = bv_to_string x1 in
             let uu____1339 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1338 uu____1339
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1343 = FStar_Options.print_real_names () in
           if uu____1343
           then
             let uu____1344 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1344
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1356 = FStar_Options.print_universes () in
        if uu____1356
        then
          let uu____1360 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1366 =
                      let uu____1369 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1369 in
                    match uu____1366 with
                    | (us,td) ->
                        let uu____1372 =
                          let uu____1379 =
                            let uu____1380 = FStar_Syntax_Subst.compress td in
                            uu____1380.FStar_Syntax_Syntax.n in
                          match uu____1379 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1389,(t,uu____1391)::(d,uu____1393)::[])
                              -> (t, d)
                          | uu____1427 -> failwith "Impossibe" in
                        (match uu____1372 with
                         | (t,d) ->
                             let uu___220_1444 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___220_1444.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___220_1444.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1360)
        else lbs in
      let uu____1448 = quals_to_string' quals in
      let uu____1449 =
        let uu____1450 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1456 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1457 =
                    let uu____1458 = FStar_Options.print_universes () in
                    if uu____1458
                    then
                      let uu____1459 =
                        let uu____1460 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1460 ">" in
                      Prims.strcat "<" uu____1459
                    else "" in
                  let uu____1462 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1463 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1456 uu____1457
                    uu____1462 uu____1463)) in
        FStar_Util.concat_l "\n and " uu____1450 in
      FStar_Util.format3 "%slet %s %s" uu____1448
        (if fst lbs1 then "rec" else "") uu____1449
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1469 = FStar_Options.print_effect_args () in
    if uu____1469
    then
      let uu____1470 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1470
    else
      (let uu____1472 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1473 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1472 uu____1473)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___214_1475  ->
      match uu___214_1475 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1477 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1481 =
        let uu____1482 = FStar_Options.ugly () in
        Prims.op_Negation uu____1482 in
      if uu____1481
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1486 = b in
         match uu____1486 with
         | (a,imp) ->
             let uu____1489 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1489
             then
               let uu____1490 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1490
             else
               (let uu____1492 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1493 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1493) in
                if uu____1492
                then
                  let uu____1494 = nm_to_string a in
                  imp_to_string uu____1494 imp
                else
                  (let uu____1496 =
                     let uu____1497 = nm_to_string a in
                     let uu____1498 =
                       let uu____1499 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1499 in
                     Prims.strcat uu____1497 uu____1498 in
                   imp_to_string uu____1496 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1505 = FStar_Options.print_implicits () in
        if uu____1505 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1507 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1507 (FStar_String.concat sep)
      else
        (let uu____1512 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1512 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___215_1516  ->
    match uu___215_1516 with
    | (a,imp) ->
        let uu____1524 = term_to_string a in imp_to_string uu____1524 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1527 = FStar_Options.print_implicits () in
      if uu____1527 then args else filter_imp args in
    let uu____1531 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1531 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1539 =
      let uu____1540 = FStar_Options.ugly () in Prims.op_Negation uu____1540 in
    if uu____1539
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1545) ->
           let uu____1552 =
             let uu____1553 = FStar_Syntax_Subst.compress t in
             uu____1553.FStar_Syntax_Syntax.n in
           (match uu____1552 with
            | FStar_Syntax_Syntax.Tm_type uu____1556 when
                let uu____1557 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1557 -> term_to_string t
            | uu____1558 ->
                let uu____1559 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1559)
       | FStar_Syntax_Syntax.GTotal (t,uu____1561) ->
           let uu____1568 =
             let uu____1569 = FStar_Syntax_Subst.compress t in
             uu____1569.FStar_Syntax_Syntax.n in
           (match uu____1568 with
            | FStar_Syntax_Syntax.Tm_type uu____1572 when
                let uu____1573 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1573 -> term_to_string t
            | uu____1574 ->
                let uu____1575 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1575)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1578 = FStar_Options.print_effect_args () in
             if uu____1578
             then
               let uu____1579 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1580 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1581 =
                 let uu____1582 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1582 (FStar_String.concat ", ") in
               let uu____1594 =
                 let uu____1595 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1595 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1579
                 uu____1580 uu____1581 uu____1594
             else
               (let uu____1601 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___216_1603  ->
                           match uu___216_1603 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1604 -> false)))
                    &&
                    (let uu____1605 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1605) in
                if uu____1601
                then
                  let uu____1606 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1606
                else
                  (let uu____1608 =
                     ((let uu____1609 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1609) &&
                        (let uu____1610 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1610))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1608
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1612 =
                        (let uu____1613 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1613) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___217_1615  ->
                                   match uu___217_1615 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1616 -> false))) in
                      if uu____1612
                      then
                        let uu____1617 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1617
                      else
                        (let uu____1619 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1620 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1619 uu____1620)))) in
           let dec =
             let uu____1622 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___218_1626  ->
                       match uu___218_1626 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1631 =
                             let uu____1632 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1632 in
                           [uu____1631]
                       | uu____1633 -> [])) in
             FStar_All.pipe_right uu____1622 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1636 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1646 = FStar_Options.print_universes () in
    if uu____1646 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1652 =
      let uu____1653 = FStar_Options.ugly () in Prims.op_Negation uu____1653 in
    if uu____1652
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1657 = s in
       match uu____1657 with
       | (us,t) ->
           let uu____1662 =
             let uu____1663 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1663 in
           let uu____1664 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1662 uu____1664)
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
          let uu____1683 =
            let uu____1684 = FStar_Options.ugly () in
            Prims.op_Negation uu____1684 in
          if uu____1683
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1694 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1699 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1700 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1701 =
                           let uu____1702 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1702 in
                         let uu____1703 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1704 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1699
                           uu____1700 uu____1701 uu____1703 uu____1704)) in
               FStar_All.pipe_right uu____1694 (FStar_String.concat ",\n\t") in
             let uu____1706 =
               let uu____1708 =
                 let uu____1710 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1711 =
                   let uu____1713 =
                     let uu____1714 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1714 in
                   let uu____1715 =
                     let uu____1717 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1718 =
                       let uu____1720 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1721 =
                         let uu____1723 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1724 =
                           let uu____1726 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1727 =
                             let uu____1729 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1730 =
                               let uu____1732 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1733 =
                                 let uu____1735 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1736 =
                                   let uu____1738 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1739 =
                                     let uu____1741 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1742 =
                                       let uu____1744 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1745 =
                                         let uu____1747 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1748 =
                                           let uu____1750 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1751 =
                                             let uu____1753 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1754 =
                                               let uu____1756 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1757 =
                                                 let uu____1759 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1760 =
                                                   let uu____1762 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1762] in
                                                 uu____1759 :: uu____1760 in
                                               uu____1756 :: uu____1757 in
                                             uu____1753 :: uu____1754 in
                                           uu____1750 :: uu____1751 in
                                         uu____1747 :: uu____1748 in
                                       uu____1744 :: uu____1745 in
                                     uu____1741 :: uu____1742 in
                                   uu____1738 :: uu____1739 in
                                 uu____1735 :: uu____1736 in
                               uu____1732 :: uu____1733 in
                             uu____1729 :: uu____1730 in
                           uu____1726 :: uu____1727 in
                         uu____1723 :: uu____1724 in
                       uu____1720 :: uu____1721 in
                     uu____1717 :: uu____1718 in
                   uu____1713 :: uu____1715 in
                 uu____1710 :: uu____1711 in
               (if for_free then "_for_free " else "") :: uu____1708 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1706)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1776 =
      let uu____1777 = FStar_Options.ugly () in Prims.op_Negation uu____1777 in
    if uu____1776
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1782 -> ""
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
           (lid,univs1,tps,k,uu____1791,uu____1792) ->
           let uu____1797 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1798 = binders_to_string " " tps in
           let uu____1799 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1797
             lid.FStar_Ident.str uu____1798 uu____1799
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1803,uu____1804,uu____1805) ->
           let uu____1808 = FStar_Options.print_universes () in
           if uu____1808
           then
             let uu____1809 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1809 with
              | (univs2,t1) ->
                  let uu____1814 = univ_names_to_string univs2 in
                  let uu____1815 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1814
                    lid.FStar_Ident.str uu____1815)
           else
             (let uu____1817 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1817)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1821 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1821 with
            | (univs2,t1) ->
                let uu____1826 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1827 =
                  let uu____1828 = FStar_Options.print_universes () in
                  if uu____1828
                  then
                    let uu____1829 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1829
                  else "" in
                let uu____1831 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1826
                  lid.FStar_Ident.str uu____1827 uu____1831)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1834 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1834
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1836,uu____1837) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1843 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1843
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1845) ->
           let uu____1850 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1850 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1862) -> lift_wp
             | (uu____1866,Some lift) -> lift in
           let uu____1871 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1871 with
            | (us,t) ->
                let uu____1878 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1879 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1880 = univ_names_to_string us in
                let uu____1881 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1878
                  uu____1879 uu____1880 uu____1881)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1889 = FStar_Options.print_universes () in
           if uu____1889
           then
             let uu____1890 =
               let uu____1893 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1893 in
             (match uu____1890 with
              | (univs2,t) ->
                  let uu____1904 =
                    let uu____1912 =
                      let uu____1913 = FStar_Syntax_Subst.compress t in
                      uu____1913.FStar_Syntax_Syntax.n in
                    match uu____1912 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1940 -> failwith "impossible" in
                  (match uu____1904 with
                   | (tps1,c1) ->
                       let uu____1960 = sli l in
                       let uu____1961 = univ_names_to_string univs2 in
                       let uu____1962 = binders_to_string " " tps1 in
                       let uu____1963 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1960
                         uu____1961 uu____1962 uu____1963))
           else
             (let uu____1965 = sli l in
              let uu____1966 = binders_to_string " " tps in
              let uu____1967 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1965 uu____1966
                uu____1967))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1976 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1976 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1981,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1983;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1985;
                       FStar_Syntax_Syntax.lbdef = uu____1986;_}::[]),uu____1987,uu____1988)
        ->
        let uu____2004 = lbname_to_string lb in
        let uu____2005 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2004 uu____2005
    | uu____2006 ->
        let uu____2007 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2007 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2017 = sli m.FStar_Syntax_Syntax.name in
    let uu____2018 =
      let uu____2019 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2019 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2017 uu____2018
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___219_2025  ->
    match uu___219_2025 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2028 = FStar_Util.string_of_int i in
        let uu____2029 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2028 uu____2029
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2032 = bv_to_string x in
        let uu____2033 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2032 uu____2033
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2040 = bv_to_string x in
        let uu____2041 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2040 uu____2041
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2044 = FStar_Util.string_of_int i in
        let uu____2045 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2044 uu____2045
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2048 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2048
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2053 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2053 (FStar_String.concat "; ")
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
       (let uu____2107 = f x in
        FStar_Util.string_builder_append strb uu____2107);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2111 = f x1 in
             FStar_Util.string_builder_append strb uu____2111)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2143 = f x in
        FStar_Util.string_builder_append strb uu____2143);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2147 = f x1 in
             FStar_Util.string_builder_append strb uu____2147)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)