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
let is_inr uu___181_173 =
  match uu___181_173 with
  | FStar_Util.Inl uu____176 -> false
  | FStar_Util.Inr uu____177 -> true 
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___182_208  ->
          match uu___182_208 with
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
  fun uu___183_448  ->
    match uu___183_448 with
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
    | FStar_Syntax_Syntax.Tm_let uu____542 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____550 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____559,m) ->
        let uu____597 = FStar_ST.read m  in
        (match uu____597 with
         | None  -> "Tm_delayed"
         | Some uu____608 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____613 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
  
let uvar_to_string u =
  let uu____627 = FStar_Options.hide_uvar_nums ()  in
  if uu____627
  then "?"
  else
    (let uu____629 =
       let uu____630 = FStar_Unionfind.uvar_id u  in
       FStar_All.pipe_right uu____630 FStar_Util.string_of_int  in
     Prims.strcat "?" uu____629)
  
let rec int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe Prims.option)
  =
  fun n1  ->
    fun u  ->
      let uu____640 = FStar_Syntax_Subst.compress_univ u  in
      match uu____640 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____646 -> (n1, (Some u))
  
let rec univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____651 = FStar_Syntax_Subst.compress_univ u  in
    match uu____651 with
    | FStar_Syntax_Syntax.U_unif u1 -> uvar_to_string u1
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "u" (Prims.strcat x.FStar_Ident.idText "u")
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____658 = FStar_Util.string_of_int x  in
        Prims.strcat "@" uu____658
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____660 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____660 with
         | (n1,None ) -> FStar_Util.string_of_int n1
         | (n1,Some u2) ->
             let uu____669 = univ_to_string u2  in
             let uu____670 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____669 uu____670)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____673 =
          let uu____674 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____674 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____673
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____682 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____682 (FStar_String.concat ", ")
  
let enclose_universes : Prims.string -> Prims.string =
  fun s  ->
    let uu____688 = FStar_Options.print_universes ()  in
    if uu____688 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let univ_names_to_string : FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____695 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____695 (FStar_String.concat ", ")
  
let qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___184_701  ->
    match uu___184_701 with
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
  
let rec term_to_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let x1 = FStar_Syntax_Subst.compress x  in
    let x2 =
      let uu____815 = FStar_Options.print_implicits ()  in
      if uu____815 then x1 else FStar_Syntax_Util.unmeta x1  in
    match x2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____817 -> failwith "impossible"
    | FStar_Syntax_Syntax.Tm_app (uu____838,[]) -> failwith "Empty args!"
    | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps) ->
        let pats =
          let uu____865 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____881 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____889  ->
                              match uu____889 with
                              | (t1,uu____893) -> term_to_string t1))
                       in
                    FStar_All.pipe_right uu____881 (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____865 (FStar_String.concat "\\/")  in
        let uu____896 = term_to_string t  in
        FStar_Util.format2 "{:pattern %s} %s" pats uu____896
    | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_monadic (m,t'))
        ->
        let uu____908 = tag_of_term t  in
        let uu____909 = sli m  in
        let uu____910 = term_to_string t'  in
        let uu____911 = term_to_string t  in
        FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____908 uu____909
          uu____910 uu____911
    | FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
        let uu____924 = tag_of_term t  in
        let uu____925 = term_to_string t'  in
        let uu____926 = sli m0  in
        let uu____927 = sli m1  in
        let uu____928 = term_to_string t  in
        FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____924
          uu____925 uu____926 uu____927 uu____928
    | FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
        FStar_Options.print_implicits () ->
        let uu____937 = FStar_Range.string_of_range r  in
        let uu____938 = term_to_string t  in
        FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____937 uu____938
    | FStar_Syntax_Syntax.Tm_meta (t,uu____940) -> term_to_string t
    | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
    | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
    | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____949) -> uvar_to_string u
    | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Tm_type u ->
        let uu____967 = FStar_Options.print_universes ()  in
        if uu____967
        then
          let uu____968 = univ_to_string u  in
          FStar_Util.format1 "Type u#(%s)" uu____968
        else "Type"
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____982 = binders_to_string " -> " bs  in
        let uu____983 = comp_to_string c  in
        FStar_Util.format2 "(%s -> %s)" uu____982 uu____983
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
        (match lc with
         | Some (FStar_Util.Inl l) when FStar_Options.print_implicits () ->
             let uu____1018 = binders_to_string " " bs  in
             let uu____1019 = term_to_string t2  in
             let uu____1020 =
               let uu____1021 = l.FStar_Syntax_Syntax.lcomp_as_comp ()  in
               FStar_All.pipe_left comp_to_string uu____1021  in
             FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1018
               uu____1019 uu____1020
         | Some (FStar_Util.Inr (l,flags)) when
             FStar_Options.print_implicits () ->
             let uu____1034 = binders_to_string " " bs  in
             let uu____1035 = term_to_string t2  in
             FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
               uu____1034 uu____1035 l.FStar_Ident.str
         | uu____1036 ->
             let uu____1043 = binders_to_string " " bs  in
             let uu____1044 = term_to_string t2  in
             FStar_Util.format2 "(fun %s -> %s)" uu____1043 uu____1044)
    | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
        let uu____1051 = bv_to_string xt  in
        let uu____1052 =
          FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string  in
        let uu____1055 = FStar_All.pipe_right f formula_to_string  in
        FStar_Util.format3 "(%s:%s{%s})" uu____1051 uu____1052 uu____1055
    | FStar_Syntax_Syntax.Tm_app (t,args) ->
        let uu____1074 = term_to_string t  in
        let uu____1075 = args_to_string args  in
        FStar_Util.format2 "(%s %s)" uu____1074 uu____1075
    | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
        let uu____1088 = lbs_to_string [] lbs  in
        let uu____1089 = term_to_string e  in
        FStar_Util.format2 "%s\nin\n%s" uu____1088 uu____1089
    | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,eff_name) ->
        let uu____1111 = term_to_string e  in
        let uu____1112 =
          let uu____1113 =
            FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
          FStar_All.pipe_right uu____1113 (FStar_Util.dflt "default")  in
        let uu____1116 = term_to_string t  in
        FStar_Util.format3 "(%s <: [%s] %s)" uu____1111 uu____1112 uu____1116
    | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inr c,uu____1119) ->
        let uu____1138 = term_to_string e  in
        let uu____1139 = comp_to_string c  in
        FStar_Util.format2 "(%s <: %s)" uu____1138 uu____1139
    | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
        let uu____1168 = term_to_string head1  in
        let uu____1169 =
          let uu____1170 =
            FStar_All.pipe_right branches
              (FStar_List.map
                 (fun uu____1188  ->
                    match uu____1188 with
                    | (p,wopt,e) ->
                        let uu____1198 = FStar_All.pipe_right p pat_to_string
                           in
                        let uu____1199 =
                          match wopt with
                          | None  -> ""
                          | Some w ->
                              let uu____1201 =
                                FStar_All.pipe_right w term_to_string  in
                              FStar_Util.format1 "when %s" uu____1201
                           in
                        let uu____1202 =
                          FStar_All.pipe_right e term_to_string  in
                        FStar_Util.format3 "%s %s -> %s" uu____1198
                          uu____1199 uu____1202))
             in
          FStar_Util.concat_l "\n\t|" uu____1170  in
        FStar_Util.format2 "(match %s with\n\t| %s)" uu____1168 uu____1169
    | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
        let uu____1209 = FStar_Options.print_universes ()  in
        if uu____1209
        then
          let uu____1210 = term_to_string t  in
          let uu____1211 = univs_to_string us  in
          FStar_Util.format2 "%s<%s>" uu____1210 uu____1211
        else term_to_string t
    | uu____1213 -> tag_of_term x2

and pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
        let uu____1227 = fv_to_string l  in
        let uu____1228 =
          let uu____1229 =
            FStar_List.map
              (fun uu____1233  ->
                 match uu____1233 with
                 | (x1,b) ->
                     let p = pat_to_string x1  in
                     if b then Prims.strcat "#" p else p) pats
             in
          FStar_All.pipe_right uu____1229 (FStar_String.concat " ")  in
        FStar_Util.format2 "(%s %s)" uu____1227 uu____1228
    | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1242) ->
        let uu____1247 = FStar_Options.print_bound_var_types ()  in
        if uu____1247
        then
          let uu____1248 = bv_to_string x1  in
          let uu____1249 = term_to_string x1.FStar_Syntax_Syntax.sort  in
          FStar_Util.format2 ".%s:%s" uu____1248 uu____1249
        else
          (let uu____1251 = bv_to_string x1  in
           FStar_Util.format1 ".%s" uu____1251)
    | FStar_Syntax_Syntax.Pat_var x1 ->
        let uu____1253 = FStar_Options.print_bound_var_types ()  in
        if uu____1253
        then
          let uu____1254 = bv_to_string x1  in
          let uu____1255 = term_to_string x1.FStar_Syntax_Syntax.sort  in
          FStar_Util.format2 "%s:%s" uu____1254 uu____1255
        else bv_to_string x1
    | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Pat_wild x1 ->
        let uu____1259 = FStar_Options.print_real_names ()  in
        if uu____1259
        then
          let uu____1260 = bv_to_string x1  in
          Prims.strcat "Pat_wild " uu____1260
        else "_"
    | FStar_Syntax_Syntax.Pat_disj ps ->
        let uu____1266 = FStar_List.map pat_to_string ps  in
        FStar_Util.concat_l " | " uu____1266

and lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1278 = FStar_Options.print_universes ()  in
        if uu____1278
        then
          let uu____1282 =
            FStar_All.pipe_right (Prims.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1288 =
                      let uu____1291 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1291
                       in
                    match uu____1288 with
                    | (us,td) ->
                        let uu____1294 =
                          let uu____1301 =
                            let uu____1302 = FStar_Syntax_Subst.compress td
                               in
                            uu____1302.FStar_Syntax_Syntax.n  in
                          match uu____1301 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1311,(t,uu____1313)::(d,uu____1315)::[])
                              -> (t, d)
                          | uu____1349 -> failwith "Impossibe"  in
                        (match uu____1294 with
                         | (t,d) ->
                             let uu___191_1366 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___191_1366.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___191_1366.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             })))
             in
          ((Prims.fst lbs), uu____1282)
        else lbs  in
      let uu____1370 = quals_to_string' quals  in
      let uu____1371 =
        let uu____1372 =
          FStar_All.pipe_right (Prims.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1378 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1379 =
                    let uu____1380 = FStar_Options.print_universes ()  in
                    if uu____1380
                    then
                      let uu____1381 =
                        let uu____1382 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1382 ">"  in
                      Prims.strcat "<" uu____1381
                    else ""  in
                  let uu____1384 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1385 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1378 uu____1379
                    uu____1384 uu____1385))
           in
        FStar_Util.concat_l "\n and " uu____1372  in
      FStar_Util.format3 "%slet %s %s" uu____1370
        (if Prims.fst lbs1 then "rec" else "") uu____1371

and lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1391 = FStar_Options.print_effect_args ()  in
    if uu____1391
    then
      let uu____1392 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
      comp_to_string uu____1392
    else
      (let uu____1394 = sli lc.FStar_Syntax_Syntax.lcomp_name  in
       let uu____1395 = term_to_string lc.FStar_Syntax_Syntax.lcomp_res_typ
          in
       FStar_Util.format2 "%s %s" uu____1394 uu____1395)

and imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.string
  =
  fun s  ->
    fun uu___185_1397  ->
      match uu___185_1397 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1399 -> s

and binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) -> Prims.string
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1405 = b  in
      match uu____1405 with
      | (a,imp) ->
          let uu____1410 = FStar_Syntax_Syntax.is_null_binder b  in
          if uu____1410
          then
            let uu____1411 = term_to_string a.FStar_Syntax_Syntax.sort  in
            Prims.strcat "_:" uu____1411
          else
            (let uu____1413 =
               (Prims.op_Negation is_arrow) &&
                 (let uu____1414 = FStar_Options.print_bound_var_types ()  in
                  Prims.op_Negation uu____1414)
                in
             if uu____1413
             then
               let uu____1415 = nm_to_string a  in
               imp_to_string uu____1415 imp
             else
               (let uu____1417 =
                  let uu____1418 = nm_to_string a  in
                  let uu____1419 =
                    let uu____1420 =
                      term_to_string a.FStar_Syntax_Syntax.sort  in
                    Prims.strcat ":" uu____1420  in
                  Prims.strcat uu____1418 uu____1419  in
                imp_to_string uu____1417 imp))

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
        let uu____1430 = FStar_Options.print_implicits ()  in
        if uu____1430 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1432 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1432 (FStar_String.concat sep)
      else
        (let uu____1439 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1439 (FStar_String.concat sep))

and arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)
    -> Prims.string
  =
  fun uu___186_1445  ->
    match uu___186_1445 with
    | (a,imp) ->
        let uu____1453 = term_to_string a  in imp_to_string uu____1453 imp

and args_to_string : FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1456 = FStar_Options.print_implicits ()  in
      if uu____1456 then args else filter_imp args  in
    let uu____1460 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1460 (FStar_String.concat " ")

and comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1469) ->
        let uu____1476 =
          let uu____1477 = FStar_Syntax_Subst.compress t  in
          uu____1477.FStar_Syntax_Syntax.n  in
        (match uu____1476 with
         | FStar_Syntax_Syntax.Tm_type uu____1480 when
             let uu____1481 = FStar_Options.print_implicits ()  in
             Prims.op_Negation uu____1481 -> term_to_string t
         | uu____1482 ->
             let uu____1483 = term_to_string t  in
             FStar_Util.format1 "Tot %s" uu____1483)
    | FStar_Syntax_Syntax.GTotal (t,uu____1485) ->
        let uu____1492 =
          let uu____1493 = FStar_Syntax_Subst.compress t  in
          uu____1493.FStar_Syntax_Syntax.n  in
        (match uu____1492 with
         | FStar_Syntax_Syntax.Tm_type uu____1496 when
             let uu____1497 = FStar_Options.print_implicits ()  in
             Prims.op_Negation uu____1497 -> term_to_string t
         | uu____1498 ->
             let uu____1499 = term_to_string t  in
             FStar_Util.format1 "GTot %s" uu____1499)
    | FStar_Syntax_Syntax.Comp c1 ->
        let basic =
          let uu____1502 = FStar_Options.print_effect_args ()  in
          if uu____1502
          then
            let uu____1503 = sli c1.FStar_Syntax_Syntax.comp_typ_name  in
            let uu____1504 =
              let uu____1505 =
                univs_to_string c1.FStar_Syntax_Syntax.comp_univs  in
              enclose_universes uu____1505  in
            let uu____1506 =
              let uu____1507 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map arg_to_string)
                 in
              FStar_All.pipe_right uu____1507 (FStar_String.concat " ")  in
            let uu____1519 =
              let uu____1520 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_List.map cflags_to_string)
                 in
              FStar_All.pipe_right uu____1520 (FStar_String.concat " ")  in
            FStar_Util.format4 "%s%s %s (attributes %s)" uu____1503
              uu____1504 uu____1506 uu____1519
          else
            (let uu____1526 =
               (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___187_1528  ->
                        match uu___187_1528 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____1529 -> false)))
                 &&
                 (let uu____1530 = FStar_Options.print_effect_args ()  in
                  Prims.op_Negation uu____1530)
                in
             if uu____1526
             then
               let uu____1531 =
                 let uu____1532 =
                   let uu____1533 =
                     FStar_List.hd c1.FStar_Syntax_Syntax.effect_args  in
                   Prims.fst uu____1533  in
                 term_to_string uu____1532  in
               FStar_Util.format1 "Tot %s" uu____1531
             else
               (let uu____1545 =
                  ((let uu____1546 = FStar_Options.print_effect_args ()  in
                    Prims.op_Negation uu____1546) &&
                     (let uu____1547 = FStar_Options.print_implicits ()  in
                      Prims.op_Negation uu____1547))
                    &&
                    (FStar_Ident.lid_equals
                       c1.FStar_Syntax_Syntax.comp_typ_name
                       FStar_Syntax_Const.effect_ML_lid)
                   in
                if uu____1545
                then "UN"
                else
                  (let uu____1549 =
                     (let uu____1550 = FStar_Options.print_effect_args ()  in
                      Prims.op_Negation uu____1550) &&
                       (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                          (FStar_Util.for_some
                             (fun uu___188_1552  ->
                                match uu___188_1552 with
                                | FStar_Syntax_Syntax.MLEFFECT  -> true
                                | uu____1553 -> false)))
                      in
                   if uu____1549
                   then
                     let uu____1554 =
                       let uu____1555 =
                         let uu____1556 =
                           FStar_List.hd c1.FStar_Syntax_Syntax.effect_args
                            in
                         Prims.fst uu____1556  in
                       term_to_string uu____1555  in
                     FStar_Util.format1 "ALL %s" uu____1554
                   else
                     (let n1 =
                        (FStar_List.length c1.FStar_Syntax_Syntax.effect_args)
                          - (Prims.parse_int "1")
                         in
                      let effect_args_wo_wp =
                        if n1 <= (Prims.parse_int "0")
                        then c1.FStar_Syntax_Syntax.effect_args
                        else
                          (let uu____1588 =
                             FStar_Util.first_N n1
                               c1.FStar_Syntax_Syntax.effect_args
                              in
                           Prims.fst uu____1588)
                         in
                      let uu____1615 =
                        sli c1.FStar_Syntax_Syntax.comp_typ_name  in
                      let uu____1616 =
                        let uu____1617 =
                          univs_to_string c1.FStar_Syntax_Syntax.comp_univs
                           in
                        enclose_universes uu____1617  in
                      let uu____1618 =
                        let uu____1619 =
                          FStar_All.pipe_right effect_args_wo_wp
                            (FStar_List.map arg_to_string)
                           in
                        FStar_All.pipe_right uu____1619
                          (FStar_String.concat " ")
                         in
                      FStar_Util.format3 "%s%s (%s)" uu____1615 uu____1616
                        uu____1618))))
           in
        let dec =
          let uu____1632 =
            FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
              (FStar_List.collect
                 (fun uu___189_1636  ->
                    match uu___189_1636 with
                    | FStar_Syntax_Syntax.DECREASES e ->
                        let uu____1641 =
                          let uu____1642 = term_to_string e  in
                          FStar_Util.format1 " (decreases %s)" uu____1642  in
                        [uu____1641]
                    | uu____1643 -> []))
             in
          FStar_All.pipe_right uu____1632 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____1646 -> ""

and formula_to_string :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi

let tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun uu____1654  ->
    match uu____1654 with
    | (us,t) ->
        let uu____1659 =
          let uu____1660 = univ_names_to_string us  in
          FStar_All.pipe_left enclose_universes uu____1660  in
        let uu____1661 = term_to_string t  in
        FStar_Util.format2 "%s%s" uu____1659 uu____1661
  
let eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  ->
      let actions_to_string actions =
        let uu____1674 =
          FStar_All.pipe_right actions
            (FStar_List.map
               (fun a  ->
                  let uu____1679 = sli a.FStar_Syntax_Syntax.action_name  in
                  let uu____1680 =
                    let uu____1681 =
                      univ_names_to_string a.FStar_Syntax_Syntax.action_univs
                       in
                    FStar_All.pipe_left enclose_universes uu____1681  in
                  let uu____1682 =
                    term_to_string a.FStar_Syntax_Syntax.action_typ  in
                  let uu____1683 =
                    term_to_string a.FStar_Syntax_Syntax.action_defn  in
                  FStar_Util.format4 "%s%s : %s = %s" uu____1679 uu____1680
                    uu____1682 uu____1683))
           in
        FStar_All.pipe_right uu____1674 (FStar_String.concat ",\n\t")  in
      let uu____1685 =
        let uu____1687 =
          let uu____1689 = lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____1690 =
            let uu____1692 =
              let uu____1693 =
                univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
              FStar_All.pipe_left enclose_universes uu____1693  in
            let uu____1694 =
              let uu____1696 =
                binders_to_string " " ed.FStar_Syntax_Syntax.binders  in
              let uu____1697 =
                let uu____1699 =
                  term_to_string ed.FStar_Syntax_Syntax.signature  in
                let uu____1700 =
                  let uu____1702 =
                    tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp  in
                  let uu____1703 =
                    let uu____1705 =
                      tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp  in
                    let uu____1706 =
                      let uu____1708 =
                        tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else
                         in
                      let uu____1709 =
                        let uu____1711 =
                          tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp  in
                        let uu____1712 =
                          let uu____1714 =
                            tscheme_to_string ed.FStar_Syntax_Syntax.stronger
                             in
                          let uu____1715 =
                            let uu____1717 =
                              tscheme_to_string
                                ed.FStar_Syntax_Syntax.close_wp
                               in
                            let uu____1718 =
                              let uu____1720 =
                                tscheme_to_string
                                  ed.FStar_Syntax_Syntax.assert_p
                                 in
                              let uu____1721 =
                                let uu____1723 =
                                  tscheme_to_string
                                    ed.FStar_Syntax_Syntax.assume_p
                                   in
                                let uu____1724 =
                                  let uu____1726 =
                                    tscheme_to_string
                                      ed.FStar_Syntax_Syntax.null_wp
                                     in
                                  let uu____1727 =
                                    let uu____1729 =
                                      tscheme_to_string
                                        ed.FStar_Syntax_Syntax.trivial
                                       in
                                    let uu____1730 =
                                      let uu____1732 =
                                        term_to_string
                                          ed.FStar_Syntax_Syntax.repr
                                         in
                                      let uu____1733 =
                                        let uu____1735 =
                                          tscheme_to_string
                                            ed.FStar_Syntax_Syntax.bind_repr
                                           in
                                        let uu____1736 =
                                          let uu____1738 =
                                            tscheme_to_string
                                              ed.FStar_Syntax_Syntax.return_repr
                                             in
                                          let uu____1739 =
                                            let uu____1741 =
                                              actions_to_string
                                                ed.FStar_Syntax_Syntax.actions
                                               in
                                            [uu____1741]  in
                                          uu____1738 :: uu____1739  in
                                        uu____1735 :: uu____1736  in
                                      uu____1732 :: uu____1733  in
                                    uu____1729 :: uu____1730  in
                                  uu____1726 :: uu____1727  in
                                uu____1723 :: uu____1724  in
                              uu____1720 :: uu____1721  in
                            uu____1717 :: uu____1718  in
                          uu____1714 :: uu____1715  in
                        uu____1711 :: uu____1712  in
                      uu____1708 :: uu____1709  in
                    uu____1705 :: uu____1706  in
                  uu____1702 :: uu____1703  in
                uu____1699 :: uu____1700  in
              uu____1696 :: uu____1697  in
            uu____1692 :: uu____1694  in
          uu____1689 :: uu____1690  in
        (if for_free then "_for_free " else "") :: uu____1687  in
      FStar_Util.format
        "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
        uu____1685
  
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.LightOff ,uu____1746) -> "#light \"off\""
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.ResetOptions (None ),uu____1747) ->
        "#reset-options"
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.ResetOptions (Some s),uu____1749) ->
        FStar_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.SetOptions s,uu____1751) ->
        FStar_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,univs,tps,k,uu____1756,uu____1757,quals,uu____1759) ->
        let uu____1766 = quals_to_string' quals  in
        let uu____1767 = binders_to_string " " tps  in
        let uu____1768 = term_to_string k  in
        FStar_Util.format4 "%stype %s %s : %s" uu____1766 lid.FStar_Ident.str
          uu____1767 uu____1768
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,univs,t,uu____1772,uu____1773,uu____1774,uu____1775,uu____1776)
        ->
        let uu____1781 = FStar_Options.print_universes ()  in
        if uu____1781
        then
          let uu____1782 = FStar_Syntax_Subst.open_univ_vars univs t  in
          (match uu____1782 with
           | (univs1,t1) ->
               let uu____1787 = univ_names_to_string univs1  in
               let uu____1788 = term_to_string t1  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____1787
                 lid.FStar_Ident.str uu____1788)
        else
          (let uu____1790 = term_to_string t  in
           FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
             uu____1790)
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t,quals,uu____1795) ->
        let uu____1798 = FStar_Syntax_Subst.open_univ_vars univs t  in
        (match uu____1798 with
         | (univs1,t1) ->
             let uu____1803 = quals_to_string' quals  in
             let uu____1804 =
               let uu____1805 = FStar_Options.print_universes ()  in
               if uu____1805
               then
                 let uu____1806 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____1806
               else ""  in
             let uu____1808 = term_to_string t1  in
             FStar_Util.format4 "%sval %s %s : %s" uu____1803
               lid.FStar_Ident.str uu____1804 uu____1808)
    | FStar_Syntax_Syntax.Sig_assume (lid,f,uu____1811,uu____1812) ->
        let uu____1815 = term_to_string f  in
        FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1815
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____1817,uu____1818,qs,uu____1820)
        -> lbs_to_string qs lbs
    | FStar_Syntax_Syntax.Sig_main (e,uu____1828) ->
        let uu____1829 = term_to_string e  in
        FStar_Util.format1 "let _ = %s" uu____1829
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1831,uu____1832,uu____1833)
        ->
        let uu____1840 = FStar_List.map sigelt_to_string ses  in
        FStar_All.pipe_right uu____1840 (FStar_String.concat "\n")
    | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____1844) ->
        eff_decl_to_string false ed
    | FStar_Syntax_Syntax.Sig_new_effect_for_free (ed,uu____1846) ->
        eff_decl_to_string true ed
    | FStar_Syntax_Syntax.Sig_sub_effect (se,r) ->
        let lift_wp =
          match ((se.FStar_Syntax_Syntax.sub_eff_lift_wp),
                  (se.FStar_Syntax_Syntax.sub_eff_lift))
          with
          | (None ,None ) -> failwith "impossible"
          | (Some lift_wp,uu____1855) -> lift_wp
          | (uu____1859,Some lift) -> lift  in
        let t = lift_wp  in
        let uu____1865 =
          let uu____1866 =
            FStar_Syntax_Syntax.mk_Comp se.FStar_Syntax_Syntax.sub_eff_source
             in
          comp_to_string uu____1866  in
        let uu____1867 =
          let uu____1868 =
            FStar_Syntax_Syntax.mk_Comp se.FStar_Syntax_Syntax.sub_eff_target
             in
          comp_to_string uu____1868  in
        let uu____1869 =
          univ_names_to_string se.FStar_Syntax_Syntax.sub_eff_univs  in
        let uu____1870 = term_to_string t  in
        FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1865
          uu____1867 uu____1869 uu____1870
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (l,univs,tps,c,uu____1875,flags,uu____1877) ->
        let uu____1882 = FStar_Options.print_universes ()  in
        if uu____1882
        then
          let uu____1883 =
            let uu____1886 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (tps, c)))
                None FStar_Range.dummyRange
               in
            FStar_Syntax_Subst.open_univ_vars univs uu____1886  in
          (match uu____1883 with
           | (univs1,t) ->
               let uu____1897 =
                 let uu____1905 =
                   let uu____1906 = FStar_Syntax_Subst.compress t  in
                   uu____1906.FStar_Syntax_Syntax.n  in
                 match uu____1905 with
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                 | uu____1933 -> failwith "impossible"  in
               (match uu____1897 with
                | (tps1,c1) ->
                    let uu____1953 = sli l  in
                    let uu____1954 = univ_names_to_string univs1  in
                    let uu____1955 = binders_to_string " " tps1  in
                    let uu____1956 = comp_to_string c1  in
                    FStar_Util.format4 "effect %s<%s> %s = %s" uu____1953
                      uu____1954 uu____1955 uu____1956))
        else
          (let uu____1958 = sli l  in
           let uu____1959 = binders_to_string " " tps  in
           let uu____1960 = comp_to_string c  in
           FStar_Util.format3 "effect %s %s = %s" uu____1958 uu____1959
             uu____1960)
  
let format_error : FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1967 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____1967 msg
  
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1971,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1973;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1975;
                       FStar_Syntax_Syntax.lbdef = uu____1976;_}::[]),uu____1977,uu____1978,uu____1979,uu____1980)
        ->
        let uu____1998 = lbname_to_string lb  in
        let uu____1999 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____1998 uu____1999
    | uu____2000 ->
        let uu____2001 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2001 (FStar_String.concat ", ")
  
let rec modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2010 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2011 =
      let uu____2012 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2012 (FStar_String.concat "\n")  in
    FStar_Util.format2 "module %s\n%s" uu____2010 uu____2011
  
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___190_2017  ->
    match uu___190_2017 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2020 = FStar_Util.string_of_int i  in
        let uu____2021 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2020 uu____2021
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2024 = bv_to_string x  in
        let uu____2025 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2024 uu____2025
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2032 = bv_to_string x  in
        let uu____2033 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2032 uu____2033
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2036 = FStar_Util.string_of_int i  in
        let uu____2037 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2036 uu____2037
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2040 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2040
  
let subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2044 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2044 (FStar_String.concat "; ")
  
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
            (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.lcomp_name))
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
       (let uu____2094 = f x  in
        FStar_Util.string_builder_append strb uu____2094);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2098 = f x1  in
             FStar_Util.string_builder_append strb uu____2098)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
  
let set_to_string f s =
  let elts = FStar_Util.set_elements s  in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder ()  in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2127 = f x  in
        FStar_Util.string_builder_append strb uu____2127);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2131 = f x1  in
             FStar_Util.string_builder_append strb uu____2131)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)
  