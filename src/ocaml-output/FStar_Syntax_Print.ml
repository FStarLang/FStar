open Prims
let sli : FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____4 = FStar_Options.print_real_names ()  in
    if uu____4
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let lid_to_string : FStar_Ident.lid -> Prims.string = fun l  -> sli l 
let fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____19 =
      let uu____20 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____20  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____19
  
let nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____24 = FStar_Options.print_real_names ()  in
    if uu____24
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let db_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____29 =
      let uu____30 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____30  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____29
  
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
  | uu____109 -> false 
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____126 -> failwith "get_lid" 
let is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e 
let is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e 
let quants : (FStar_Ident.lident * Prims.string) Prims.list =
  [(FStar_Syntax_Const.forall_lid, "forall");
  (FStar_Syntax_Const.exists_lid, "exists")] 
type exp = FStar_Syntax_Syntax.term
let is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.b2t_lid] t 
let is_quant : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op (Prims.fst (FStar_List.split quants)) t 
let is_ite : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.ite_lid] t 
let is_lex_cons : exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lexcons_lid] f 
let is_lex_top : exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lextop_lid] f 
let is_inr uu___198_173 =
  match uu___198_173 with
  | FStar_Util.Inl uu____176 -> false
  | FStar_Util.Inr uu____177 -> true 
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___199_208  ->
          match uu___199_208 with
          | (uu____212,Some (FStar_Syntax_Syntax.Implicit uu____213)) ->
              false
          | uu____215 -> true))
  
let rec reconstruct_lex :
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list Prims.option
  =
  fun e  ->
    let uu____226 =
      let uu____227 = FStar_Syntax_Subst.compress e  in
      uu____227.FStar_Syntax_Syntax.n  in
    match uu____226 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map Prims.fst args1  in
        let uu____273 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____273
        then
          let uu____282 =
            let uu____287 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____287  in
          (match uu____282 with
           | Some xs ->
               let uu____301 =
                 let uu____305 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____305 :: xs  in
               Some uu____301
           | None  -> None)
        else None
    | uu____325 ->
        let uu____326 = is_lex_top e  in if uu____326 then Some [] else None
  
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____362 = f hd1  in if uu____362 then hd1 else find f tl1
  
let find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____376 =
        find (fun p  -> FStar_Ident.lid_equals x (Prims.fst p)) xs  in
      Prims.snd uu____376
  
let infix_prim_op_to_string e =
  let uu____395 = get_lid e  in find_lid uu____395 infix_prim_ops 
let unary_prim_op_to_string e =
  let uu____407 = get_lid e  in find_lid uu____407 unary_prim_ops 
let quant_to_string t =
  let uu____419 = get_lid t  in find_lid uu____419 quants 
let const_to_string : FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____427) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____430 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____435) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____445 = sli l  in
        FStar_Util.format1 "[[%s.reflect]]" uu____445
  
let lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___200_448  ->
    match uu___200_448 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let tag_of_term : FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____459 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____459
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____461 = nm_to_string x  in Prims.strcat "Tm_name: " uu____461
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____463 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____463
    | FStar_Syntax_Syntax.Tm_uinst uu____468 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____473 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____474 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____475 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____490 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____498 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____503 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____513 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____529 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____547 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____555 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____564,m) ->
        let uu____602 = FStar_ST.read m  in
        (match uu____602 with
         | None  -> "Tm_delayed"
         | Some uu____613 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____618 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
  
let uvar_to_string u =
  let uu____632 = FStar_Options.hide_uvar_nums ()  in
  if uu____632
  then "?"
  else
    (let uu____634 =
       let uu____635 = FStar_Unionfind.uvar_id u  in
       FStar_All.pipe_right uu____635 FStar_Util.string_of_int  in
     Prims.strcat "?" uu____634)
  
let rec int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe Prims.option)
  =
  fun n1  ->
    fun u  ->
      let uu____645 = FStar_Syntax_Subst.compress_univ u  in
      match uu____645 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____651 -> (n1, (Some u))
  
let rec univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____656 = FStar_Syntax_Subst.compress_univ u  in
    match uu____656 with
    | FStar_Syntax_Syntax.U_unif u1 -> uvar_to_string u1
    | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____663 = FStar_Util.string_of_int x  in
        Prims.strcat "@" uu____663
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____665 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____665 with
         | (n1,None ) -> FStar_Util.string_of_int n1
         | (n1,Some u2) ->
             let uu____674 = univ_to_string u2  in
             let uu____675 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____674 uu____675)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____678 =
          let uu____679 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____679 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____678
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____687 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____687 (FStar_String.concat ", ")
  
let univ_names_to_string : FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____695 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____695 (FStar_String.concat ", ")
  
let qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___201_701  ->
    match uu___201_701 with
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
        let uu____703 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____703
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____706 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____706 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____713 =
          let uu____714 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____714  in
        let uu____716 =
          let uu____717 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____717 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____713 uu____716
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____728 =
          let uu____729 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____729  in
        let uu____731 =
          let uu____732 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____732 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____728 uu____731
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____738 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____738
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
    | uu____745 ->
        let uu____747 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____747 (FStar_String.concat " ")
  
let quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____757 ->
        let uu____759 = quals_to_string quals  in Prims.strcat uu____759 " "
  
let term_to_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let e = FStar_Syntax_Resugar.resugar_term x  in
    FStar_Parser_AST.term_to_string e
  
let rec pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
        let uu____825 = fv_to_string l  in
        let uu____826 =
          let uu____827 =
            FStar_List.map
              (fun uu____831  ->
                 match uu____831 with
                 | (x1,b) ->
                     let p = pat_to_string x1  in
                     if b then Prims.strcat "#" p else p) pats
             in
          FStar_All.pipe_right uu____827 (FStar_String.concat " ")  in
        FStar_Util.format2 "(%s %s)" uu____825 uu____826
    | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____840) ->
        let uu____845 = FStar_Options.print_bound_var_types ()  in
        if uu____845
        then
          let uu____846 = bv_to_string x1  in
          let uu____847 = term_to_string x1.FStar_Syntax_Syntax.sort  in
          FStar_Util.format2 ".%s:%s" uu____846 uu____847
        else
          (let uu____849 = bv_to_string x1  in
           FStar_Util.format1 ".%s" uu____849)
    | FStar_Syntax_Syntax.Pat_var x1 ->
        let uu____851 = FStar_Options.print_bound_var_types ()  in
        if uu____851
        then
          let uu____852 = bv_to_string x1  in
          let uu____853 = term_to_string x1.FStar_Syntax_Syntax.sort  in
          FStar_Util.format2 "%s:%s" uu____852 uu____853
        else bv_to_string x1
    | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Pat_wild x1 ->
        let uu____857 = FStar_Options.print_real_names ()  in
        if uu____857
        then
          let uu____858 = bv_to_string x1  in
          Prims.strcat "Pat_wild " uu____858
        else "_"
    | FStar_Syntax_Syntax.Pat_disj ps ->
        let uu____864 = FStar_List.map pat_to_string ps  in
        FStar_Util.concat_l " | " uu____864

and lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____876 = FStar_Options.print_universes ()  in
        if uu____876
        then
          let uu____880 =
            FStar_All.pipe_right (Prims.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____886 =
                      let uu____889 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____889
                       in
                    match uu____886 with
                    | (us,td) ->
                        let uu____892 =
                          let uu____899 =
                            let uu____900 = FStar_Syntax_Subst.compress td
                               in
                            uu____900.FStar_Syntax_Syntax.n  in
                          match uu____899 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____909,(t,uu____911)::(d,uu____913)::[]) ->
                              (t, d)
                          | uu____947 -> failwith "Impossibe"  in
                        (match uu____892 with
                         | (t,d) ->
                             let uu___208_964 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___208_964.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___208_964.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             })))
             in
          ((Prims.fst lbs), uu____880)
        else lbs  in
      let uu____968 = quals_to_string' quals  in
      let uu____969 =
        let uu____970 =
          FStar_All.pipe_right (Prims.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____976 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____977 =
                    let uu____978 = FStar_Options.print_universes ()  in
                    if uu____978
                    then
                      let uu____979 =
                        let uu____980 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____980 ">"  in
                      Prims.strcat "<" uu____979
                    else ""  in
                  let uu____982 = term_to_string lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let uu____983 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format4 "%s %s : %s = %s" uu____976 uu____977
                    uu____982 uu____983))
           in
        FStar_Util.concat_l "\n and " uu____970  in
      FStar_Util.format3 "%slet %s %s" uu____968
        (if Prims.fst lbs1 then "rec" else "") uu____969

and lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____989 = FStar_Options.print_effect_args ()  in
    if uu____989
    then
      let uu____990 = lc.FStar_Syntax_Syntax.comp ()  in
      comp_to_string uu____990
    else
      (let uu____992 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____993 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____992 uu____993)

and imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.string
  =
  fun s  ->
    fun uu___202_995  ->
      match uu___202_995 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____997 -> s

and binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) -> Prims.string
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1003 = b  in
      match uu____1003 with
      | (a,imp) ->
          let uu____1008 = FStar_Syntax_Syntax.is_null_binder b  in
          if uu____1008
          then
            let uu____1009 = term_to_string a.FStar_Syntax_Syntax.sort  in
            Prims.strcat "_:" uu____1009
          else
            (let uu____1011 =
               (Prims.op_Negation is_arrow) &&
                 (let uu____1012 = FStar_Options.print_bound_var_types ()  in
                  Prims.op_Negation uu____1012)
                in
             if uu____1011
             then
               let uu____1013 = nm_to_string a  in
               imp_to_string uu____1013 imp
             else
               (let uu____1015 =
                  let uu____1016 = nm_to_string a  in
                  let uu____1017 =
                    let uu____1018 =
                      term_to_string a.FStar_Syntax_Syntax.sort  in
                    Prims.strcat ":" uu____1018  in
                  Prims.strcat uu____1016 uu____1017  in
                imp_to_string uu____1015 imp))

and binder_to_string :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) -> Prims.string =
  fun b  -> binder_to_string' false b

and arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) -> Prims.string =
  fun b  -> binder_to_string' true b

and binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1028 = FStar_Options.print_implicits ()  in
        if uu____1028 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1030 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1030 (FStar_String.concat sep)
      else
        (let uu____1037 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1037 (FStar_String.concat sep))

and arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)
    -> Prims.string
  =
  fun uu___203_1043  ->
    match uu___203_1043 with
    | (a,imp) ->
        let uu____1051 = term_to_string a  in imp_to_string uu____1051 imp

and args_to_string : FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1054 = FStar_Options.print_implicits ()  in
      if uu____1054 then args else filter_imp args  in
    let uu____1058 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1058 (FStar_String.concat " ")

and comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1067) ->
        let uu____1074 =
          let uu____1075 = FStar_Syntax_Subst.compress t  in
          uu____1075.FStar_Syntax_Syntax.n  in
        (match uu____1074 with
         | FStar_Syntax_Syntax.Tm_type uu____1078 when
             let uu____1079 = FStar_Options.print_implicits ()  in
             Prims.op_Negation uu____1079 -> term_to_string t
         | uu____1080 ->
             let uu____1081 = term_to_string t  in
             FStar_Util.format1 "Tot %s" uu____1081)
    | FStar_Syntax_Syntax.GTotal (t,uu____1083) ->
        let uu____1090 =
          let uu____1091 = FStar_Syntax_Subst.compress t  in
          uu____1091.FStar_Syntax_Syntax.n  in
        (match uu____1090 with
         | FStar_Syntax_Syntax.Tm_type uu____1094 when
             let uu____1095 = FStar_Options.print_implicits ()  in
             Prims.op_Negation uu____1095 -> term_to_string t
         | uu____1096 ->
             let uu____1097 = term_to_string t  in
             FStar_Util.format1 "GTot %s" uu____1097)
    | FStar_Syntax_Syntax.Comp c1 ->
        let basic =
          let uu____1100 = FStar_Options.print_effect_args ()  in
          if uu____1100
          then
            let uu____1101 = sli c1.FStar_Syntax_Syntax.effect_name  in
            let uu____1102 = term_to_string c1.FStar_Syntax_Syntax.result_typ
               in
            let uu____1103 =
              let uu____1104 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map arg_to_string)
                 in
              FStar_All.pipe_right uu____1104 (FStar_String.concat ", ")  in
            let uu____1116 =
              let uu____1117 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_List.map cflags_to_string)
                 in
              FStar_All.pipe_right uu____1117 (FStar_String.concat " ")  in
            FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1101
              uu____1102 uu____1103 uu____1116
          else
            (let uu____1123 =
               (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___204_1125  ->
                        match uu___204_1125 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____1126 -> false)))
                 &&
                 (let uu____1127 = FStar_Options.print_effect_args ()  in
                  Prims.op_Negation uu____1127)
                in
             if uu____1123
             then
               let uu____1128 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               FStar_Util.format1 "Tot %s" uu____1128
             else
               (let uu____1130 =
                  ((let uu____1131 = FStar_Options.print_effect_args ()  in
                    Prims.op_Negation uu____1131) &&
                     (let uu____1132 = FStar_Options.print_implicits ()  in
                      Prims.op_Negation uu____1132))
                    &&
                    (FStar_Ident.lid_equals
                       c1.FStar_Syntax_Syntax.effect_name
                       FStar_Syntax_Const.effect_ML_lid)
                   in
                if uu____1130
                then term_to_string c1.FStar_Syntax_Syntax.result_typ
                else
                  (let uu____1134 =
                     (let uu____1135 = FStar_Options.print_effect_args ()  in
                      Prims.op_Negation uu____1135) &&
                       (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                          (FStar_Util.for_some
                             (fun uu___205_1137  ->
                                match uu___205_1137 with
                                | FStar_Syntax_Syntax.MLEFFECT  -> true
                                | uu____1138 -> false)))
                      in
                   if uu____1134
                   then
                     let uu____1139 =
                       term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                     FStar_Util.format1 "ALL %s" uu____1139
                   else
                     (let uu____1141 = sli c1.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____1142 =
                        term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                      FStar_Util.format2 "%s (%s)" uu____1141 uu____1142))))
           in
        let dec =
          let uu____1144 =
            FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
              (FStar_List.collect
                 (fun uu___206_1148  ->
                    match uu___206_1148 with
                    | FStar_Syntax_Syntax.DECREASES e ->
                        let uu____1153 =
                          let uu____1154 = term_to_string e  in
                          FStar_Util.format1 " (decreases %s)" uu____1154  in
                        [uu____1153]
                    | uu____1155 -> []))
             in
          FStar_All.pipe_right uu____1144 (FStar_String.concat " ")  in
        FStar_Util.format2 "%s%s" basic dec

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
    | FStar_Syntax_Syntax.DECREASES uu____1158 -> ""

and formula_to_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun phi  -> term_to_string phi

let enclose_universes : Prims.string -> Prims.string =
  fun s  ->
    let uu____1165 = FStar_Options.print_universes ()  in
    if uu____1165 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun uu____1169  ->
    match uu____1169 with
    | (us,t) ->
        let uu____1174 =
          let uu____1175 = univ_names_to_string us  in
          FStar_All.pipe_left enclose_universes uu____1175  in
        let uu____1176 = term_to_string t  in
        FStar_Util.format2 "%s%s" uu____1174 uu____1176
  
let eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  ->
      let actions_to_string actions =
        let uu____1189 =
          FStar_All.pipe_right actions
            (FStar_List.map
               (fun a  ->
                  let uu____1194 = sli a.FStar_Syntax_Syntax.action_name  in
                  let uu____1195 =
                    let uu____1196 =
                      univ_names_to_string a.FStar_Syntax_Syntax.action_univs
                       in
                    FStar_All.pipe_left enclose_universes uu____1196  in
                  let uu____1197 =
                    term_to_string a.FStar_Syntax_Syntax.action_typ  in
                  let uu____1198 =
                    term_to_string a.FStar_Syntax_Syntax.action_defn  in
                  FStar_Util.format4 "%s%s : %s = %s" uu____1194 uu____1195
                    uu____1197 uu____1198))
           in
        FStar_All.pipe_right uu____1189 (FStar_String.concat ",\n\t")  in
      let uu____1200 =
        let uu____1202 =
          let uu____1204 = lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____1205 =
            let uu____1207 =
              let uu____1208 =
                univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
              FStar_All.pipe_left enclose_universes uu____1208  in
            let uu____1209 =
              let uu____1211 =
                binders_to_string " " ed.FStar_Syntax_Syntax.binders  in
              let uu____1212 =
                let uu____1214 =
                  term_to_string ed.FStar_Syntax_Syntax.signature  in
                let uu____1215 =
                  let uu____1217 =
                    tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp  in
                  let uu____1218 =
                    let uu____1220 =
                      tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp  in
                    let uu____1221 =
                      let uu____1223 =
                        tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else
                         in
                      let uu____1224 =
                        let uu____1226 =
                          tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp  in
                        let uu____1227 =
                          let uu____1229 =
                            tscheme_to_string ed.FStar_Syntax_Syntax.stronger
                             in
                          let uu____1230 =
                            let uu____1232 =
                              tscheme_to_string
                                ed.FStar_Syntax_Syntax.close_wp
                               in
                            let uu____1233 =
                              let uu____1235 =
                                tscheme_to_string
                                  ed.FStar_Syntax_Syntax.assert_p
                                 in
                              let uu____1236 =
                                let uu____1238 =
                                  tscheme_to_string
                                    ed.FStar_Syntax_Syntax.assume_p
                                   in
                                let uu____1239 =
                                  let uu____1241 =
                                    tscheme_to_string
                                      ed.FStar_Syntax_Syntax.null_wp
                                     in
                                  let uu____1242 =
                                    let uu____1244 =
                                      tscheme_to_string
                                        ed.FStar_Syntax_Syntax.trivial
                                       in
                                    let uu____1245 =
                                      let uu____1247 =
                                        term_to_string
                                          ed.FStar_Syntax_Syntax.repr
                                         in
                                      let uu____1248 =
                                        let uu____1250 =
                                          tscheme_to_string
                                            ed.FStar_Syntax_Syntax.bind_repr
                                           in
                                        let uu____1251 =
                                          let uu____1253 =
                                            tscheme_to_string
                                              ed.FStar_Syntax_Syntax.return_repr
                                             in
                                          let uu____1254 =
                                            let uu____1256 =
                                              actions_to_string
                                                ed.FStar_Syntax_Syntax.actions
                                               in
                                            [uu____1256]  in
                                          uu____1253 :: uu____1254  in
                                        uu____1250 :: uu____1251  in
                                      uu____1247 :: uu____1248  in
                                    uu____1244 :: uu____1245  in
                                  uu____1241 :: uu____1242  in
                                uu____1238 :: uu____1239  in
                              uu____1235 :: uu____1236  in
                            uu____1232 :: uu____1233  in
                          uu____1229 :: uu____1230  in
                        uu____1226 :: uu____1227  in
                      uu____1223 :: uu____1224  in
                    uu____1220 :: uu____1221  in
                  uu____1217 :: uu____1218  in
                uu____1214 :: uu____1215  in
              uu____1211 :: uu____1212  in
            uu____1207 :: uu____1209  in
          uu____1204 :: uu____1205  in
        (if for_free then "_for_free " else "") :: uu____1202  in
      FStar_Util.format
        "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
        uu____1200
  
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
        "#light \"off\""
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None
        )) -> "#reset-options"
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some
        s)) -> FStar_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
        FStar_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,univs1,tps,k,uu____1267,uu____1268,quals) ->
        let uu____1276 = quals_to_string' quals  in
        let uu____1277 = binders_to_string " " tps  in
        let uu____1278 = term_to_string k  in
        FStar_Util.format4 "%stype %s %s : %s" uu____1276 lid.FStar_Ident.str
          uu____1277 uu____1278
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,univs1,t,uu____1282,uu____1283,uu____1284,uu____1285) ->
        let uu____1290 = FStar_Options.print_universes ()  in
        if uu____1290
        then
          let uu____1291 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          (match uu____1291 with
           | (univs2,t1) ->
               let uu____1296 = univ_names_to_string univs2  in
               let uu____1297 = term_to_string t1  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____1296
                 lid.FStar_Ident.str uu____1297)
        else
          (let uu____1299 = term_to_string t  in
           FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
             uu____1299)
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t,quals) ->
        let uu____1306 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
        (match uu____1306 with
         | (univs2,t1) ->
             let uu____1311 = quals_to_string' quals  in
             let uu____1312 =
               let uu____1313 = FStar_Options.print_universes ()  in
               if uu____1313
               then
                 let uu____1314 = univ_names_to_string univs2  in
                 FStar_Util.format1 "<%s>" uu____1314
               else ""  in
             let uu____1316 = term_to_string t1  in
             FStar_Util.format4 "%sval %s %s : %s" uu____1311
               lid.FStar_Ident.str uu____1312 uu____1316)
    | FStar_Syntax_Syntax.Sig_assume (lid,f,uu____1319) ->
        let uu____1322 = term_to_string f  in
        FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1322
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____1324,qs,uu____1326) ->
        lbs_to_string qs lbs
    | FStar_Syntax_Syntax.Sig_main e ->
        let uu____1334 = term_to_string e  in
        FStar_Util.format1 "let _ = %s" uu____1334
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1336,uu____1337) ->
        let uu____1344 = FStar_List.map sigelt_to_string ses  in
        FStar_All.pipe_right uu____1344 (FStar_String.concat "\n")
    | FStar_Syntax_Syntax.Sig_new_effect ed -> eff_decl_to_string false ed
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        eff_decl_to_string true ed
    | FStar_Syntax_Syntax.Sig_sub_effect se ->
        let lift_wp =
          match ((se.FStar_Syntax_Syntax.lift_wp),
                  (se.FStar_Syntax_Syntax.lift))
          with
          | (None ,None ) -> failwith "impossible"
          | (Some lift_wp,uu____1356) -> lift_wp
          | (uu____1360,Some lift) -> lift  in
        let uu____1365 =
          FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp)
            (Prims.snd lift_wp)
           in
        (match uu____1365 with
         | (us,t) ->
             let uu____1372 = lid_to_string se.FStar_Syntax_Syntax.source  in
             let uu____1373 = lid_to_string se.FStar_Syntax_Syntax.target  in
             let uu____1374 = univ_names_to_string us  in
             let uu____1375 = term_to_string t  in
             FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1372
               uu____1373 uu____1374 uu____1375)
    | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,uu____1380,flags)
        ->
        let uu____1386 = FStar_Options.print_universes ()  in
        if uu____1386
        then
          let uu____1387 =
            let uu____1390 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (tps, c)))
                None FStar_Range.dummyRange
               in
            FStar_Syntax_Subst.open_univ_vars univs1 uu____1390  in
          (match uu____1387 with
           | (univs2,t) ->
               let uu____1401 =
                 let uu____1409 =
                   let uu____1410 = FStar_Syntax_Subst.compress t  in
                   uu____1410.FStar_Syntax_Syntax.n  in
                 match uu____1409 with
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                 | uu____1437 -> failwith "impossible"  in
               (match uu____1401 with
                | (tps1,c1) ->
                    let uu____1457 = sli l  in
                    let uu____1458 = univ_names_to_string univs2  in
                    let uu____1459 = binders_to_string " " tps1  in
                    let uu____1460 = comp_to_string c1  in
                    FStar_Util.format4 "effect %s<%s> %s = %s" uu____1457
                      uu____1458 uu____1459 uu____1460))
        else
          (let uu____1462 = sli l  in
           let uu____1463 = binders_to_string " " tps  in
           let uu____1464 = comp_to_string c  in
           FStar_Util.format3 "effect %s %s = %s" uu____1462 uu____1463
             uu____1464)
  
let format_error : FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1471 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____1471 msg
  
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1475,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1477;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1479;
                       FStar_Syntax_Syntax.lbdef = uu____1480;_}::[]),uu____1481,uu____1482,uu____1483)
        ->
        let uu____1501 = lbname_to_string lb  in
        let uu____1502 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____1501 uu____1502
    | uu____1503 ->
        let uu____1504 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____1504 (FStar_String.concat ", ")
  
let rec modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1513 = sli m.FStar_Syntax_Syntax.name  in
    let uu____1514 =
      let uu____1515 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____1515 (FStar_String.concat "\n")  in
    FStar_Util.format2 "module %s\n%s" uu____1513 uu____1514
  
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___207_1520  ->
    match uu___207_1520 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1523 = FStar_Util.string_of_int i  in
        let uu____1524 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1523 uu____1524
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1527 = bv_to_string x  in
        let uu____1528 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1527 uu____1528
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1535 = bv_to_string x  in
        let uu____1536 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____1535 uu____1536
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1539 = FStar_Util.string_of_int i  in
        let uu____1540 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1539 uu____1540
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1543 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1543
  
let subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1547 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1547 (FStar_String.concat "; ")
  
let abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    Prims.option -> Prims.string
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
       (let uu____1597 = f x  in
        FStar_Util.string_builder_append strb uu____1597);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____1601 = f x1  in
             FStar_Util.string_builder_append strb uu____1601)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
  
let set_to_string f s =
  let elts = FStar_Util.set_elements s  in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder ()  in
      (FStar_Util.string_builder_append strb "{";
       (let uu____1630 = f x  in
        FStar_Util.string_builder_append strb uu____1630);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____1634 = f x1  in
             FStar_Util.string_builder_append strb uu____1634)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)
  