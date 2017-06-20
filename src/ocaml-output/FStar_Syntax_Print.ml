open Prims
let rec delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___210_3  ->
    match uu___210_3 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____5 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_defined_at_level " uu____5
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____7 =
          let uu____8 = delta_depth_to_string d  in Prims.strcat uu____8 ")"
           in
        Prims.strcat "Delta_abstract (" uu____7
  
let sli : FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____12 = FStar_Options.print_real_names ()  in
    if uu____12
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let lid_to_string : FStar_Ident.lid -> Prims.string = fun l  -> sli l 
let fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____27 =
      let uu____28 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____28  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____27
  
let nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____32 = FStar_Options.print_real_names ()  in
    if uu____32
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let db_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____37 =
      let uu____38 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____38  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____37
  
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list =
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
let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list =
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
let is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (fst (FStar_List.split infix_prim_ops)) e 
let is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (fst (FStar_List.split unary_prim_ops)) e 
let quants : (FStar_Ident.lident * Prims.string) Prims.list =
  [(FStar_Syntax_Const.forall_lid, "forall");
  (FStar_Syntax_Const.exists_lid, "exists")] 
type exp = FStar_Syntax_Syntax.term
let is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.b2t_lid] t 
let is_quant : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op (fst (FStar_List.split quants)) t 
let is_ite : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.ite_lid] t 
let is_lex_cons : exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lexcons_lid] f 
let is_lex_top : exp -> Prims.bool =
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
  
let rec reconstruct_lex :
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____234 =
      let uu____235 = FStar_Syntax_Subst.compress e  in
      uu____235.FStar_Syntax_Syntax.n  in
    match uu____234 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives.fst args1  in
        let uu____281 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____281
        then
          let uu____290 =
            let uu____295 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____295  in
          (match uu____290 with
           | Some xs ->
               let uu____309 =
                 let uu____313 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____313 :: xs  in
               Some uu____309
           | None  -> None)
        else None
    | uu____333 ->
        let uu____334 = is_lex_top e  in if uu____334 then Some [] else None
  
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____370 = f hd1  in if uu____370 then hd1 else find f tl1
  
let find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____384 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs
         in
      snd uu____384
  
let infix_prim_op_to_string e =
  let uu____403 = get_lid e  in find_lid uu____403 infix_prim_ops 
let unary_prim_op_to_string e =
  let uu____415 = get_lid e  in find_lid uu____415 unary_prim_ops 
let quant_to_string t =
  let uu____427 = get_lid t  in find_lid uu____427 quants 
let const_to_string : FStar_Const.sconst -> Prims.string =
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
        let uu____453 = sli l  in
        FStar_Util.format1 "[[%s.reflect]]" uu____453
  
let lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___213_456  ->
    match uu___213_456 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let tag_of_term : FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____467 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____467
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____469 = nm_to_string x  in Prims.strcat "Tm_name: " uu____469
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____471 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
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
        let uu____593 = FStar_ST.read m  in
        (match uu____593 with
         | None  -> "Tm_delayed"
         | Some uu____604 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____609 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
  
let uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____617 = FStar_Options.hide_uvar_nums ()  in
    if uu____617
    then "?"
    else
      (let uu____619 =
         let uu____620 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____620 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____619)
  
let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____624 = FStar_Options.hide_uvar_nums ()  in
    if uu____624
    then "?"
    else
      (let uu____626 =
         let uu____627 = FStar_Syntax_Unionfind.univ_uvar_id u  in
         FStar_All.pipe_right uu____627 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____626)
  
let rec int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____637 = FStar_Syntax_Subst.compress_univ u  in
      match uu____637 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____643 -> (n1, (Some u))
  
let rec univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____648 =
      let uu____649 = FStar_Options.ugly ()  in Prims.op_Negation uu____649
       in
    if uu____648
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____653 = FStar_Syntax_Subst.compress_univ u  in
       match uu____653 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____659 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____659
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____661 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____661 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____670 = univ_to_string u2  in
                let uu____671 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____670 uu____671)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____674 =
             let uu____675 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____675 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____674
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____683 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____683 (FStar_String.concat ", ")
  
let univ_names_to_string : FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____691 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____691 (FStar_String.concat ", ")
  
let qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string =
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
        let uu____699 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____699
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____702 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____702 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____709 =
          let uu____710 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____710  in
        let uu____712 =
          let uu____713 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____713 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____709 uu____712
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____724 =
          let uu____725 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____725  in
        let uu____727 =
          let uu____728 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____728 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____724 uu____727
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____734 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____734
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
  
let quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____741 ->
        let uu____743 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____743 (FStar_String.concat " ")
  
let quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____753 ->
        let uu____755 = quals_to_string quals  in Prims.strcat uu____755 " "
  
let rec term_to_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____803 =
      let uu____804 = FStar_Options.ugly ()  in Prims.op_Negation uu____804
       in
    if uu____803
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____810 = FStar_Options.print_implicits ()  in
         if uu____810 then x1 else FStar_Syntax_Util.unmeta x1  in
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
                                 | (t1,uu____882) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____870
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____854 (FStar_String.concat "\\/")  in
           let uu____885 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____885
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____897 = tag_of_term t  in
           let uu____898 = sli m  in
           let uu____899 = term_to_string t'  in
           let uu____900 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____897 uu____898
             uu____899 uu____900
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____913 = tag_of_term t  in
           let uu____914 = term_to_string t'  in
           let uu____915 = sli m0  in
           let uu____916 = sli m1  in
           let uu____917 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____913
             uu____914 uu____915 uu____916 uu____917
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____919,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____933 = FStar_Range.string_of_range r  in
           let uu____934 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____933
             uu____934
       | FStar_Syntax_Syntax.Tm_meta (t,uu____936) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____945) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____960 = FStar_Options.print_universes ()  in
           if uu____960
           then
             let uu____961 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____961
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____975 = binders_to_string " -> " bs  in
           let uu____976 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____975 uu____976
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some rc when FStar_Options.print_implicits () ->
                let uu____993 = binders_to_string " " bs  in
                let uu____994 = term_to_string t2  in
                let uu____995 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____999 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____999)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____993 uu____994
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____995
            | uu____1002 ->
                let uu____1004 = binders_to_string " " bs  in
                let uu____1005 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1004 uu____1005)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1012 = bv_to_string xt  in
           let uu____1013 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1016 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1012 uu____1013 uu____1016
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1035 = term_to_string t  in
           let uu____1036 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1035 uu____1036
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1049 = lbs_to_string [] lbs  in
           let uu____1050 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1049 uu____1050
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1098 =
                   let uu____1099 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1099
                     (FStar_Util.dflt "default")
                    in
                 let uu____1102 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1098 uu____1102
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1118 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1118
              in
           let uu____1119 = term_to_string e  in
           FStar_Util.format3 "(%s <: %s %s)" uu____1119 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1148 = term_to_string head1  in
           let uu____1149 =
             let uu____1150 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1168  ->
                       match uu____1168 with
                       | (p,wopt,e) ->
                           let uu____1178 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1179 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1181 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1181
                              in
                           let uu____1182 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1178
                             uu____1179 uu____1182))
                in
             FStar_Util.concat_l "\n\t|" uu____1150  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1148 uu____1149
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1189 = FStar_Options.print_universes ()  in
           if uu____1189
           then
             let uu____1190 = term_to_string t  in
             let uu____1191 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1190 uu____1191
           else term_to_string t
       | uu____1193 -> tag_of_term x2)

and pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1195 =
      let uu____1196 = FStar_Options.ugly ()  in Prims.op_Negation uu____1196
       in
    if uu____1195
    then
      let e = FStar_Syntax_Resugar.resugar_pat x  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1212 = fv_to_string l  in
           let uu____1213 =
             let uu____1214 =
               FStar_List.map
                 (fun uu____1218  ->
                    match uu____1218 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1214 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1212 uu____1213
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1227) ->
           let uu____1232 = FStar_Options.print_bound_var_types ()  in
           if uu____1232
           then
             let uu____1233 = bv_to_string x1  in
             let uu____1234 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1233 uu____1234
           else
             (let uu____1236 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1236)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1238 = FStar_Options.print_bound_var_types ()  in
           if uu____1238
           then
             let uu____1239 = bv_to_string x1  in
             let uu____1240 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1239 uu____1240
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1244 = FStar_Options.print_real_names ()  in
           if uu____1244
           then
             let uu____1245 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1245
           else "_")

and lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1257 = FStar_Options.print_universes ()  in
        if uu____1257
        then
          let uu____1261 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1267 =
                      let uu____1270 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1270
                       in
                    match uu____1267 with
                    | (us,td) ->
                        let uu____1273 =
                          let uu____1280 =
                            let uu____1281 = FStar_Syntax_Subst.compress td
                               in
                            uu____1281.FStar_Syntax_Syntax.n  in
                          match uu____1280 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1290,(t,uu____1292)::(d,uu____1294)::[])
                              -> (t, d)
                          | uu____1328 -> failwith "Impossibe"  in
                        (match uu____1273 with
                         | (t,d) ->
                             let uu___221_1345 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___221_1345.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___221_1345.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             })))
             in
          ((fst lbs), uu____1261)
        else lbs  in
      let uu____1349 = quals_to_string' quals  in
      let uu____1350 =
        let uu____1351 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1357 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1358 =
                    let uu____1359 = FStar_Options.print_universes ()  in
                    if uu____1359
                    then
                      let uu____1360 =
                        let uu____1361 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1361 ">"  in
                      Prims.strcat "<" uu____1360
                    else ""  in
                  let uu____1363 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1364 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1357 uu____1358
                    uu____1363 uu____1364))
           in
        FStar_Util.concat_l "\n and " uu____1351  in
      FStar_Util.format3 "%slet %s %s" uu____1349
        (if fst lbs1 then "rec" else "") uu____1350

and lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1370 = FStar_Options.print_effect_args ()  in
    if uu____1370
    then
      let uu____1371 = lc.FStar_Syntax_Syntax.comp ()  in
      comp_to_string uu____1371
    else
      (let uu____1373 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1374 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1373 uu____1374)

and imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___215_1376  ->
      match uu___215_1376 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1378 -> s

and binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1382 =
        let uu____1383 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1383  in
      if uu____1382
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange
           in
        let d = FStar_Parser_ToDocument.binder_to_document e  in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1387 = b  in
         match uu____1387 with
         | (a,imp) ->
             let uu____1390 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1390
             then
               let uu____1391 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1391
             else
               (let uu____1393 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1394 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1394)
                   in
                if uu____1393
                then
                  let uu____1395 = nm_to_string a  in
                  imp_to_string uu____1395 imp
                else
                  (let uu____1397 =
                     let uu____1398 = nm_to_string a  in
                     let uu____1399 =
                       let uu____1400 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1400  in
                     Prims.strcat uu____1398 uu____1399  in
                   imp_to_string uu____1397 imp)))

and binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b

and arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b

and binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1406 = FStar_Options.print_implicits ()  in
        if uu____1406 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1408 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1408 (FStar_String.concat sep)
      else
        (let uu____1413 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1413 (FStar_String.concat sep))

and arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___216_1417  ->
    match uu___216_1417 with
    | (a,imp) ->
        let uu____1425 = term_to_string a  in imp_to_string uu____1425 imp

and args_to_string : FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1428 = FStar_Options.print_implicits ()  in
      if uu____1428 then args else filter_imp args  in
    let uu____1432 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1432 (FStar_String.concat " ")

and comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1440 =
      let uu____1441 = FStar_Options.ugly ()  in Prims.op_Negation uu____1441
       in
    if uu____1440
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1446) ->
           let uu____1453 =
             let uu____1454 = FStar_Syntax_Subst.compress t  in
             uu____1454.FStar_Syntax_Syntax.n  in
           (match uu____1453 with
            | FStar_Syntax_Syntax.Tm_type uu____1457 when
                let uu____1458 = FStar_Options.print_implicits ()  in
                Prims.op_Negation uu____1458 -> term_to_string t
            | uu____1459 ->
                let uu____1460 = term_to_string t  in
                FStar_Util.format1 "Tot %s" uu____1460)
       | FStar_Syntax_Syntax.GTotal (t,uu____1462) ->
           let uu____1469 =
             let uu____1470 = FStar_Syntax_Subst.compress t  in
             uu____1470.FStar_Syntax_Syntax.n  in
           (match uu____1469 with
            | FStar_Syntax_Syntax.Tm_type uu____1473 when
                let uu____1474 = FStar_Options.print_implicits ()  in
                Prims.op_Negation uu____1474 -> term_to_string t
            | uu____1475 ->
                let uu____1476 = term_to_string t  in
                FStar_Util.format1 "GTot %s" uu____1476)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1479 = FStar_Options.print_effect_args ()  in
             if uu____1479
             then
               let uu____1480 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____1481 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____1482 =
                 let uu____1483 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____1483 (FStar_String.concat ", ")
                  in
               let uu____1495 =
                 let uu____1496 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____1496 (FStar_String.concat " ")
                  in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1480
                 uu____1481 uu____1482 uu____1495
             else
               (let uu____1502 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___217_1504  ->
                           match uu___217_1504 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1505 -> false)))
                    &&
                    (let uu____1506 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____1506)
                   in
                if uu____1502
                then
                  let uu____1507 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____1507
                else
                  (let uu____1509 =
                     ((let uu____1510 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____1510) &&
                        (let uu____1511 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____1511))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid)
                      in
                   if uu____1509
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1513 =
                        (let uu____1514 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____1514) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___218_1516  ->
                                   match uu___218_1516 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1517 -> false)))
                         in
                      if uu____1513
                      then
                        let uu____1518 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____1518
                      else
                        (let uu____1520 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____1521 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____1520 uu____1521))))
              in
           let dec =
             let uu____1523 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___219_1527  ->
                       match uu___219_1527 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1532 =
                             let uu____1533 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____1533
                              in
                           [uu____1532]
                       | uu____1534 -> []))
                in
             FStar_All.pipe_right uu____1523 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and cflags_to_string : FStar_Syntax_Syntax.cflags -> Prims.string =
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____1537 -> ""

and formula_to_string :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi

let enclose_universes : Prims.string -> Prims.string =
  fun s  ->
    let uu____1546 = FStar_Options.print_universes ()  in
    if uu____1546 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1551 =
      let uu____1552 = FStar_Options.ugly ()  in Prims.op_Negation uu____1552
       in
    if uu____1551
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1556 = s  in
       match uu____1556 with
       | (us,t) ->
           let uu____1561 =
             let uu____1562 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____1562  in
           let uu____1563 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____1561 uu____1563)
  
let action_to_string : FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____1567 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____1568 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____1569 =
      let uu____1570 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____1570  in
    let uu____1571 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____1572 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____1567 uu____1568 uu____1569
      uu____1571 uu____1572
  
let eff_decl_to_string' :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____1587 =
            let uu____1588 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____1588  in
          if uu____1587
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1598 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____1598 (FStar_String.concat ",\n\t")
                in
             let uu____1603 =
               let uu____1605 =
                 let uu____1607 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____1608 =
                   let uu____1610 =
                     let uu____1611 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____1611  in
                   let uu____1612 =
                     let uu____1614 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____1615 =
                       let uu____1617 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____1618 =
                         let uu____1620 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____1621 =
                           let uu____1623 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____1624 =
                             let uu____1626 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____1627 =
                               let uu____1629 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____1630 =
                                 let uu____1632 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____1633 =
                                   let uu____1635 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____1636 =
                                     let uu____1638 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____1639 =
                                       let uu____1641 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____1642 =
                                         let uu____1644 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____1645 =
                                           let uu____1647 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____1648 =
                                             let uu____1650 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____1651 =
                                               let uu____1653 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____1654 =
                                                 let uu____1656 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____1657 =
                                                   let uu____1659 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____1659]  in
                                                 uu____1656 :: uu____1657  in
                                               uu____1653 :: uu____1654  in
                                             uu____1650 :: uu____1651  in
                                           uu____1647 :: uu____1648  in
                                         uu____1644 :: uu____1645  in
                                       uu____1641 :: uu____1642  in
                                     uu____1638 :: uu____1639  in
                                   uu____1635 :: uu____1636  in
                                 uu____1632 :: uu____1633  in
                               uu____1629 :: uu____1630  in
                             uu____1626 :: uu____1627  in
                           uu____1623 :: uu____1624  in
                         uu____1620 :: uu____1621  in
                       uu____1617 :: uu____1618  in
                     uu____1614 :: uu____1615  in
                   uu____1610 :: uu____1612  in
                 uu____1607 :: uu____1608  in
               (if for_free then "_for_free " else "") :: uu____1605  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1603)
  
let eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1670 =
      let uu____1671 = FStar_Options.ugly ()  in Prims.op_Negation uu____1671
       in
    if uu____1670
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1676 -> ""
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
           (lid,univs1,tps,k,uu____1685,uu____1686) ->
           let uu____1691 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
              in
           let uu____1692 = binders_to_string " " tps  in
           let uu____1693 = term_to_string k  in
           FStar_Util.format4 "%stype %s %s : %s" uu____1691
             lid.FStar_Ident.str uu____1692 uu____1693
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1697,uu____1698,uu____1699) ->
           let uu____1702 = FStar_Options.print_universes ()  in
           if uu____1702
           then
             let uu____1703 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
             (match uu____1703 with
              | (univs2,t1) ->
                  let uu____1708 = univ_names_to_string univs2  in
                  let uu____1709 = term_to_string t1  in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1708
                    lid.FStar_Ident.str uu____1709)
           else
             (let uu____1711 = term_to_string t  in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1711)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1715 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
           (match uu____1715 with
            | (univs2,t1) ->
                let uu____1720 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
                let uu____1721 =
                  let uu____1722 = FStar_Options.print_universes ()  in
                  if uu____1722
                  then
                    let uu____1723 = univ_names_to_string univs2  in
                    FStar_Util.format1 "<%s>" uu____1723
                  else ""  in
                let uu____1725 = term_to_string t1  in
                FStar_Util.format4 "%sval %s %s : %s" uu____1720
                  lid.FStar_Ident.str uu____1721 uu____1725)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1728 = term_to_string f  in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1728
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1730,uu____1731) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1737 = term_to_string e  in
           FStar_Util.format1 "let _ = %s" uu____1737
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1739) ->
           let uu____1744 = FStar_List.map sigelt_to_string ses  in
           FStar_All.pipe_right uu____1744 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1756) -> lift_wp
             | (uu____1760,Some lift) -> lift  in
           let uu____1765 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp)
              in
           (match uu____1765 with
            | (us,t) ->
                let uu____1772 = lid_to_string se.FStar_Syntax_Syntax.source
                   in
                let uu____1773 = lid_to_string se.FStar_Syntax_Syntax.target
                   in
                let uu____1774 = univ_names_to_string us  in
                let uu____1775 = term_to_string t  in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1772
                  uu____1773 uu____1774 uu____1775)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1783 = FStar_Options.print_universes ()  in
           if uu____1783
           then
             let uu____1784 =
               let uu____1787 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange
                  in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1787  in
             (match uu____1784 with
              | (univs2,t) ->
                  let uu____1798 =
                    let uu____1806 =
                      let uu____1807 = FStar_Syntax_Subst.compress t  in
                      uu____1807.FStar_Syntax_Syntax.n  in
                    match uu____1806 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1834 -> failwith "impossible"  in
                  (match uu____1798 with
                   | (tps1,c1) ->
                       let uu____1854 = sli l  in
                       let uu____1855 = univ_names_to_string univs2  in
                       let uu____1856 = binders_to_string " " tps1  in
                       let uu____1857 = comp_to_string c1  in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1854
                         uu____1855 uu____1856 uu____1857))
           else
             (let uu____1859 = sli l  in
              let uu____1860 = binders_to_string " " tps  in
              let uu____1861 = comp_to_string c  in
              FStar_Util.format3 "effect %s %s = %s" uu____1859 uu____1860
                uu____1861))
  
let format_error : FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1868 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____1868 msg
  
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1872,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1874;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1876;
                       FStar_Syntax_Syntax.lbdef = uu____1877;_}::[]),uu____1878,uu____1879)
        ->
        let uu____1895 = lbname_to_string lb  in
        let uu____1896 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____1895 uu____1896
    | uu____1897 ->
        let uu____1898 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____1898 (FStar_String.concat ", ")
  
let rec modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1907 = sli m.FStar_Syntax_Syntax.name  in
    let uu____1908 =
      let uu____1909 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____1909 (FStar_String.concat "\n")  in
    FStar_Util.format2 "module %s\n%s" uu____1907 uu____1908
  
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___220_1914  ->
    match uu___220_1914 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1917 = FStar_Util.string_of_int i  in
        let uu____1918 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1917 uu____1918
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1921 = bv_to_string x  in
        let uu____1922 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1921 uu____1922
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1929 = bv_to_string x  in
        let uu____1930 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____1929 uu____1930
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1933 = FStar_Util.string_of_int i  in
        let uu____1934 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1933 uu____1934
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1937 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1937
  
let subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1941 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1941 (FStar_String.concat "; ")
  
let abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either option ->
    Prims.string
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder ()  in
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
      let strb = FStar_Util.new_string_builder ()  in
      (FStar_Util.string_builder_append strb "[";
       (let uu____1991 = f x  in
        FStar_Util.string_builder_append strb uu____1991);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____1995 = f x1  in
             FStar_Util.string_builder_append strb uu____1995)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
  
let set_to_string f s =
  let elts = FStar_Util.set_elements s  in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder ()  in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2024 = f x  in
        FStar_Util.string_builder_append strb uu____2024);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2028 = f x1  in
             FStar_Util.string_builder_append strb uu____2028)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)
  