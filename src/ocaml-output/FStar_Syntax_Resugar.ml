open Prims
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____5 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____5
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___196_37  ->
          match uu___196_37 with
          | (uu____41,Some (FStar_Syntax_Syntax.Implicit uu____42)) -> false
          | uu____44 -> true))
let resugar_arg_qual:
  FStar_Syntax_Syntax.arg_qualifier option ->
    FStar_Parser_AST.arg_qualifier option option
  =
  fun q  ->
    match q with
    | None  -> Some None
    | Some (FStar_Syntax_Syntax.Implicit b) ->
        if b then None else Some (Some FStar_Parser_AST.Implicit)
    | Some (FStar_Syntax_Syntax.Equality ) ->
        Some (Some FStar_Parser_AST.Equality)
let rec universe_to_int:
  Prims.int ->
    FStar_Syntax_Syntax.universe -> (Prims.int* FStar_Syntax_Syntax.universe)
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____78 -> (n1, u)
let rec resugar_universe:
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
      | FStar_Syntax_Syntax.U_succ uu____97 ->
          let uu____98 = universe_to_int (Prims.parse_int "0") u in
          (match uu____98 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____103 =
                      let uu____104 =
                        let uu____105 =
                          let uu____111 = FStar_Util.string_of_int n1 in
                          (uu____111, None) in
                        FStar_Const.Const_int uu____105 in
                      FStar_Parser_AST.Const uu____104 in
                    mk1 uu____103 r
                | uu____117 ->
                    let e1 =
                      let uu____119 =
                        let uu____120 =
                          let uu____121 =
                            let uu____127 = FStar_Util.string_of_int n1 in
                            (uu____127, None) in
                          FStar_Const.Const_int uu____121 in
                        FStar_Parser_AST.Const uu____120 in
                      mk1 uu____119 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____137 ->
               let t =
                 let uu____140 =
                   let uu____141 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____141 in
                 mk1 uu____140 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____144 =
                        let uu____145 =
                          let uu____149 = resugar_universe x r in
                          (acc, uu____149, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____145 in
                      mk1 uu____144 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____151 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____156 =
              let uu____159 =
                let uu____160 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____160 in
              (uu____159, r) in
            FStar_Ident.mk_ident uu____156 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op: Prims.string -> (Prims.string* Prims.int) option =
  fun s  ->
    let name_of_op uu___197_173 =
      match uu___197_173 with
      | "Amp" -> Some ("&", (Prims.parse_int "0"))
      | "At" -> Some ("@", (Prims.parse_int "0"))
      | "Plus" -> Some ("+", (Prims.parse_int "0"))
      | "Minus" -> Some ("-", (Prims.parse_int "0"))
      | "Subtraction" -> Some ("-", (Prims.parse_int "2"))
      | "Slash" -> Some ("/", (Prims.parse_int "0"))
      | "Less" -> Some ("<", (Prims.parse_int "0"))
      | "Equals" -> Some ("=", (Prims.parse_int "0"))
      | "Greater" -> Some (">", (Prims.parse_int "0"))
      | "Underscore" -> Some ("_", (Prims.parse_int "0"))
      | "Bar" -> Some ("|", (Prims.parse_int "0"))
      | "Bang" -> Some ("!", (Prims.parse_int "0"))
      | "Hat" -> Some ("^", (Prims.parse_int "0"))
      | "Percent" -> Some ("%", (Prims.parse_int "0"))
      | "Star" -> Some ("*", (Prims.parse_int "0"))
      | "Question" -> Some ("?", (Prims.parse_int "0"))
      | "Colon" -> Some (":", (Prims.parse_int "0"))
      | uu____211 -> None in
    match s with
    | "op_String_Assignment" -> Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" -> Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" -> Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" -> Some (".()", (Prims.parse_int "0"))
    | uu____225 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____231 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____231 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____238 ->
               let op =
                 let uu____241 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some (op,uu____258) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____241 in
               Some (op, (Prims.parse_int "0")))
        else None
let rec resugar_term_as_op:
  FStar_Syntax_Syntax.term -> (Prims.string* Prims.int) option =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Syntax_Const.op_Addition, "+");
      (FStar_Syntax_Const.op_Subtraction, "-");
      (FStar_Syntax_Const.op_Minus, "-");
      (FStar_Syntax_Const.op_Multiply, "*");
      (FStar_Syntax_Const.op_Division, "/");
      (FStar_Syntax_Const.op_Modulus, "%");
      (FStar_Syntax_Const.read_lid, "!");
      (FStar_Syntax_Const.list_append_lid, "@");
      (FStar_Syntax_Const.list_tot_append_lid, "@");
      (FStar_Syntax_Const.strcat_lid, "^");
      (FStar_Syntax_Const.pipe_right_lid, "|>");
      (FStar_Syntax_Const.pipe_left_lid, "<|");
      (FStar_Syntax_Const.op_Eq, "=");
      (FStar_Syntax_Const.op_ColonEq, ":=");
      (FStar_Syntax_Const.op_notEq, "<>");
      (FStar_Syntax_Const.not_lid, "~");
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
      (FStar_Syntax_Const.eq3_lid, "===");
      (FStar_Syntax_Const.forall_lid, "forall");
      (FStar_Syntax_Const.exists_lid, "exists");
      (FStar_Syntax_Const.salloc_lid, "alloc")] in
    let fallback fv =
      let uu____356 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (fst d))) in
      match uu____356 with
      | Some op -> Some ((snd op), (Prims.parse_int "0"))
      | uu____381 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1")) in
          if FStar_Util.starts_with str "dtuple"
          then Some ("dtuple", (Prims.parse_int "0"))
          else
            if FStar_Util.starts_with str "tuple"
            then Some ("tuple", (Prims.parse_int "0"))
            else
              if FStar_Util.starts_with str "try_with"
              then Some ("try_with", (Prims.parse_int "0"))
              else
                (let uu____424 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____424
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
    let uu____437 =
      let uu____438 = FStar_Syntax_Subst.compress t in
      uu____438.FStar_Syntax_Syntax.n in
    match uu____437 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1")) in
        let uu____466 = string_to_op s in
        (match uu____466 with | Some t1 -> Some t1 | uu____480 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____490 -> None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____496 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____500 -> true
    | uu____501 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____529 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____529 in
    let var a r =
      let uu____537 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____537 in
    let uu____538 =
      let uu____539 = FStar_Syntax_Subst.compress t in
      uu____539.FStar_Syntax_Syntax.n in
    match uu____538 with
    | FStar_Syntax_Syntax.Tm_delayed uu____542 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____559 = let uu____561 = bv_as_unique_ident x in [uu____561] in
          FStar_Ident.lid_of_ids uu____559 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____564 = let uu____566 = bv_as_unique_ident x in [uu____566] in
          FStar_Ident.lid_of_ids uu____564 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
        let s =
          if length1 = (Prims.parse_int "0")
          then a.FStar_Ident.str
          else
            FStar_Util.substring_from a.FStar_Ident.str
              (length1 + (Prims.parse_int "1")) in
        let is_prefix = Prims.strcat FStar_Ident.reserved_prefix "is_" in
        if FStar_Util.starts_with s is_prefix
        then
          let rest =
            FStar_Util.substring_from s (FStar_String.length is_prefix) in
          let uu____590 =
            let uu____591 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____591 in
          mk1 uu____590
        else
          if
            FStar_Util.starts_with s FStar_Syntax_Util.field_projector_prefix
          then
            (let rest =
               FStar_Util.substring_from s
                 (FStar_String.length
                    FStar_Syntax_Util.field_projector_prefix) in
             let r =
               FStar_Util.split rest FStar_Syntax_Util.field_projector_sep in
             match r with
             | fst1::snd1::[] ->
                 let l =
                   FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos in
                 let r1 =
                   FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos)) in
                 mk1 (FStar_Parser_AST.Projector (l, r1))
             | uu____602 -> failwith "wrong projector format")
          else
            (let uu____605 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____606 =
                    let uu____607 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____607 in
                  let uu____608 = FStar_String.get s (Prims.parse_int "0") in
                  uu____606 <> uu____608) in
             if uu____605
             then
               let uu____609 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____609
             else
               (let uu____611 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____611))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____618 = FStar_Options.print_universes () in
        if uu____618
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____622 =
                   let uu____623 =
                     let uu____627 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____627, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____623 in
                 mk1 uu____622) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____630 = FStar_Syntax_Syntax.is_teff t in
        if uu____630
        then
          let uu____631 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____631
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____634 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____634
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____635 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____635
         | uu____636 ->
             let uu____637 = FStar_Options.print_universes () in
             if uu____637
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____648 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____648))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____651) ->
        let uu____664 = FStar_Syntax_Subst.open_term xs body in
        (match uu____664 with
         | (xs1,body1) ->
             let xs2 =
               let uu____670 = FStar_Options.print_implicits () in
               if uu____670 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____677  ->
                       match uu____677 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____697 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____697 with
         | (xs1,body1) ->
             let xs2 =
               let uu____703 = FStar_Options.print_implicits () in
               if uu____703 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____708 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____708 FStar_List.rev in
             let rec aux body3 uu___198_721 =
               match uu___198_721 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____734 =
          let uu____737 =
            let uu____738 = FStar_Syntax_Syntax.mk_binder x in [uu____738] in
          FStar_Syntax_Subst.open_term uu____737 phi in
        (match uu____734 with
         | (x1,phi1) ->
             let b =
               let uu____742 = FStar_List.hd x1 in
               resugar_binder uu____742 t.FStar_Syntax_Syntax.pos in
             let uu____745 =
               let uu____746 =
                 let uu____749 = resugar_term phi1 in (b, uu____749) in
               FStar_Parser_AST.Refine uu____746 in
             mk1 uu____745)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___199_779 =
          match uu___199_779 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____826 -> failwith "last of an empty list" in
        let rec last_two uu___200_850 =
          match uu___200_850 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____870::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____922::t1 -> last_two t1 in
        let rec last_three uu___201_950 =
          match uu___201_950 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____970::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____988::uu____989::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1062::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1098  ->
                    match uu____1098 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1112 = FStar_Options.print_implicits () in
          if uu____1112 then args else filter_imp args in
        let uu____1121 = resugar_term_as_op e in
        (match uu____1121 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1127) ->
             (match args1 with
              | (fst1,uu____1131)::(snd1,uu____1133)::rest ->
                  let e1 =
                    let uu____1157 =
                      let uu____1158 =
                        let uu____1162 =
                          let uu____1164 = resugar_term fst1 in
                          let uu____1165 =
                            let uu____1167 = resugar_term snd1 in
                            [uu____1167] in
                          uu____1164 :: uu____1165 in
                        ((FStar_Ident.id_of_text "*"), uu____1162) in
                      FStar_Parser_AST.Op uu____1158 in
                    mk1 uu____1157 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1172  ->
                         match uu____1172 with
                         | (x,uu____1176) ->
                             let uu____1177 =
                               let uu____1178 =
                                 let uu____1182 =
                                   let uu____1184 =
                                     let uu____1186 = resugar_term x in
                                     [uu____1186] in
                                   e1 :: uu____1184 in
                                 ((FStar_Ident.id_of_text "*"), uu____1182) in
                               FStar_Parser_AST.Op uu____1178 in
                             mk1 uu____1177) e1 rest
              | uu____1188 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1194) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1216)::[] -> b
               | uu____1229 -> failwith "wrong arguments to dtuple" in
             let uu____1237 =
               let uu____1238 = FStar_Syntax_Subst.compress body in
               uu____1238.FStar_Syntax_Syntax.n in
             (match uu____1237 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1243) ->
                  let uu____1256 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1256 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1262 = FStar_Options.print_implicits () in
                         if uu____1262 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1270 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1281  ->
                            match uu____1281 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1289) -> resugar_as_app e args1
         | Some (ref_read,uu____1293) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1296 = FStar_List.hd args1 in
             (match uu____1296 with
              | (t1,uu____1306) ->
                  let uu____1311 =
                    let uu____1312 = FStar_Syntax_Subst.compress t1 in
                    uu____1312.FStar_Syntax_Syntax.n in
                  (match uu____1311 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1325 =
                         let uu____1326 =
                           let uu____1329 = resugar_term t1 in
                           (uu____1329, f) in
                         FStar_Parser_AST.Project uu____1326 in
                       mk1 uu____1325
                   | uu____1330 -> resugar_term t1))
         | Some ("try_with",uu____1331) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1347 =
               match new_args with
               | (a1,uu____1361)::(a2,uu____1363)::[] -> (a1, a2)
               | uu____1388 -> failwith "wrong arguments to try_with" in
             (match uu____1347 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1414 =
                      let uu____1415 = FStar_Syntax_Subst.compress term in
                      uu____1415.FStar_Syntax_Syntax.n in
                    match uu____1414 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1420) ->
                        let uu____1433 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1433 with | (x1,e2) -> e2)
                    | uu____1438 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1440 = decomp body in resugar_term uu____1440 in
                  let handler1 =
                    let uu____1442 = decomp handler in
                    resugar_term uu____1442 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1448,uu____1449,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1466,uu____1467,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1480 =
                          let uu____1481 =
                            let uu____1486 = resugar_body t11 in
                            (uu____1486, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1481 in
                        mk1 uu____1480
                    | uu____1488 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1521 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1537) -> resugar_as_app e args1
         | Some (op,uu____1541) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1592 -> (xs, pat, t1) in
             let resugar body =
               let uu____1600 =
                 let uu____1601 = FStar_Syntax_Subst.compress body in
                 uu____1601.FStar_Syntax_Syntax.n in
               match uu____1600 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1606) ->
                   let uu____1619 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1619 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1625 = FStar_Options.print_implicits () in
                          if uu____1625 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1631 =
                          let uu____1636 =
                            let uu____1637 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1637.FStar_Syntax_Syntax.n in
                          match uu____1636 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1677  ->
                                                 match uu____1677 with
                                                 | (e2,uu____1681) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1684) ->
                                    let uu____1685 =
                                      let uu____1687 =
                                        let uu____1688 = name s r in
                                        mk1 uu____1688 in
                                      [uu____1687] in
                                    [uu____1685]
                                | uu____1691 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1696 ->
                              let uu____1697 = resugar_term body2 in
                              ([], uu____1697) in
                        (match uu____1631 with
                         | (pats,body3) ->
                             let uu____1707 = uncurry xs3 pats body3 in
                             (match uu____1707 with
                              | (xs4,pats1,body4) ->
                                  let xs5 =
                                    FStar_All.pipe_right xs4 FStar_List.rev in
                                  if op = "forall"
                                  then
                                    mk1
                                      (FStar_Parser_AST.QForall
                                         (xs5, pats1, body4))
                                  else
                                    mk1
                                      (FStar_Parser_AST.QExists
                                         (xs5, pats1, body4)))))
               | uu____1734 ->
                   if op = "forall"
                   then
                     let uu____1735 =
                       let uu____1736 =
                         let uu____1743 = resugar_term body in
                         ([], [[]], uu____1743) in
                       FStar_Parser_AST.QForall uu____1736 in
                     mk1 uu____1735
                   else
                     (let uu____1750 =
                        let uu____1751 =
                          let uu____1758 = resugar_term body in
                          ([], [[]], uu____1758) in
                        FStar_Parser_AST.QExists uu____1751 in
                      mk1 uu____1750) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1778)::[] -> resugar b
                | uu____1791 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1798) ->
             let uu____1801 = FStar_List.hd args1 in
             (match uu____1801 with | (e1,uu____1811) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1838  ->
                       match uu____1838 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____1843 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1843 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1851 =
                         let uu____1852 =
                           let uu____1856 =
                             let uu____1858 = last1 args1 in
                             resugar uu____1858 in
                           (op1, uu____1856) in
                         FStar_Parser_AST.Op uu____1852 in
                       mk1 uu____1851
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1870 =
                         let uu____1871 =
                           let uu____1875 =
                             let uu____1877 = last_two args1 in
                             resugar uu____1877 in
                           (op1, uu____1875) in
                         FStar_Parser_AST.Op uu____1871 in
                       mk1 uu____1870
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1889 =
                         let uu____1890 =
                           let uu____1894 =
                             let uu____1896 = last_three args1 in
                             resugar uu____1896 in
                           (op1, uu____1894) in
                         FStar_Parser_AST.Op uu____1890 in
                       mk1 uu____1889
                   | uu____1901 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1909 =
                    let uu____1910 =
                      let uu____1914 =
                        let uu____1916 = last_two args1 in resugar uu____1916 in
                      (op1, uu____1914) in
                    FStar_Parser_AST.Op uu____1910 in
                  mk1 uu____1909
              | uu____1921 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1924,t1)::[]) ->
        let bnds =
          let uu____1979 =
            let uu____1982 = resugar_pat pat in
            let uu____1983 = resugar_term e in (uu____1982, uu____1983) in
          [uu____1979] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____1994,t1)::(pat2,uu____1997,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2072 =
          let uu____2073 =
            let uu____2077 = resugar_term e in
            let uu____2078 = resugar_term t1 in
            let uu____2079 = resugar_term t2 in
            (uu____2077, uu____2078, uu____2079) in
          FStar_Parser_AST.If uu____2073 in
        mk1 uu____2072
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2119 =
          match uu____2119 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2138 = resugar_term e1 in Some uu____2138 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2141 =
          let uu____2142 =
            let uu____2150 = resugar_term e in
            let uu____2151 = FStar_List.map resugar_branch branches in
            (uu____2150, uu____2151) in
          FStar_Parser_AST.Match uu____2142 in
        mk1 uu____2141
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2173) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2226 =
          let uu____2227 =
            let uu____2232 = resugar_term e in (uu____2232, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2227 in
        mk1 uu____2226
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2250 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2250 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2266 =
                 let uu____2269 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2269 in
               match uu____2266 with
               | (univs1,td) ->
                   let uu____2276 =
                     let uu____2283 =
                       let uu____2284 = FStar_Syntax_Subst.compress td in
                       uu____2284.FStar_Syntax_Syntax.n in
                     match uu____2283 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2293,(t1,uu____2295)::(d,uu____2297)::[]) ->
                         (t1, d)
                     | uu____2331 -> failwith "wrong let binding format" in
                   (match uu____2276 with
                    | (typ,def) ->
                        let uu____2352 =
                          let uu____2356 =
                            let uu____2357 = FStar_Syntax_Subst.compress def in
                            uu____2357.FStar_Syntax_Syntax.n in
                          match uu____2356 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2365) ->
                              let uu____2378 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2378 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2387 =
                                       FStar_Options.print_implicits () in
                                     if uu____2387 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2389 -> ([], def, false) in
                        (match uu____2352 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2410 =
                                 FStar_Options.print_universes () in
                               if uu____2410
                               then
                                 let uu____2411 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2411
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2416 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2427 =
                                     let uu____2428 =
                                       let uu____2429 =
                                         let uu____2433 =
                                           bv_as_unique_ident bv in
                                         (uu____2433, None) in
                                       FStar_Parser_AST.PatVar uu____2429 in
                                     mk_pat uu____2428 in
                                   (uu____2427, term) in
                             (match uu____2416 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2450  ->
                                              match uu____2450 with
                                              | (bv,uu____2454) ->
                                                  let uu____2455 =
                                                    let uu____2456 =
                                                      let uu____2460 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2460, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2456 in
                                                  mk_pat uu____2455)) in
                                    let uu____2462 =
                                      let uu____2465 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2465) in
                                    let uu____2467 =
                                      universe_to_string univs1 in
                                    (uu____2462, uu____2467)
                                  else
                                    (let uu____2471 =
                                       let uu____2474 = resugar_term term1 in
                                       (pat, uu____2474) in
                                     let uu____2475 =
                                       universe_to_string univs1 in
                                     (uu____2471, uu____2475))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2514) ->
        let s =
          let uu____2528 =
            let uu____2529 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2529 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2528 in
        let uu____2530 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2530
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___202_2540 =
          match uu___202_2540 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2541 =
                let uu____2542 = FStar_Syntax_Subst.compress e in
                uu____2542.FStar_Syntax_Syntax.n in
              (match uu____2541 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2568 =
                       let uu____2569 = FStar_Syntax_Subst.compress h in
                       uu____2569.FStar_Syntax_Syntax.n in
                     match uu____2568 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2576 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2576, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2584 = aux h1 in
                         (match uu____2584 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2596 -> failwith "wrong Data_app head format" in
                   let uu____2600 = aux head1 in
                   (match uu____2600 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2615 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2615, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2624  ->
                               match uu____2624 with
                               | (t1,uu____2630) ->
                                   let uu____2631 = resugar_term t1 in
                                   (uu____2631, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2632 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2632
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2637 = FStar_Options.print_universes () in
                           if uu____2637
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2647,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2653,uu____2654) -> resugar_term e
                    | uu____2659 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2660 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2666,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2682 =
                      let uu____2683 =
                        let uu____2688 = resugar_seq t11 in
                        (uu____2688, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2683 in
                    mk1 uu____2682
                | uu____2690 -> t1 in
              resugar_seq term
          | FStar_Syntax_Syntax.Primop  -> resugar_term e
          | FStar_Syntax_Syntax.Masked_effect  -> resugar_term e
          | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term e
          | FStar_Syntax_Syntax.Mutable_alloc  ->
              let term = resugar_term e in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier ,l,t1)
                   ->
                   mk1
                     (FStar_Parser_AST.Let (FStar_Parser_AST.Mutable, l, t1))
               | uu____2703 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2705 =
                let uu____2706 = FStar_Syntax_Subst.compress e in
                uu____2706.FStar_Syntax_Syntax.n in
              (match uu____2705 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2710;
                      FStar_Syntax_Syntax.pos = uu____2711;
                      FStar_Syntax_Syntax.vars = uu____2712;_},(term,uu____2714)::[])
                   -> resugar_term term
               | uu____2736 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2758  ->
                       match uu____2758 with
                       | (x,uu____2762) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2764,p) ->
             let uu____2766 =
               let uu____2767 =
                 let uu____2771 = resugar_term e in (uu____2771, l, p) in
               FStar_Parser_AST.Labeled uu____2767 in
             mk1 uu____2766
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2780 =
               let uu____2781 =
                 let uu____2786 = resugar_term e in
                 let uu____2787 =
                   let uu____2788 =
                     let uu____2789 =
                       let uu____2795 =
                         let uu____2799 =
                           let uu____2802 = resugar_term t1 in
                           (uu____2802, FStar_Parser_AST.Nothing) in
                         [uu____2799] in
                       (name1, uu____2795) in
                     FStar_Parser_AST.Construct uu____2789 in
                   mk1 uu____2788 in
                 (uu____2786, uu____2787, None) in
               FStar_Parser_AST.Ascribed uu____2781 in
             mk1 uu____2780
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2812,t1) ->
             let uu____2818 =
               let uu____2819 =
                 let uu____2824 = resugar_term e in
                 let uu____2825 =
                   let uu____2826 =
                     let uu____2827 =
                       let uu____2833 =
                         let uu____2837 =
                           let uu____2840 = resugar_term t1 in
                           (uu____2840, FStar_Parser_AST.Nothing) in
                         [uu____2837] in
                       (name1, uu____2833) in
                     FStar_Parser_AST.Construct uu____2827 in
                   mk1 uu____2826 in
                 (uu____2824, uu____2825, None) in
               FStar_Parser_AST.Ascribed uu____2819 in
             mk1 uu____2818)
    | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild
and resugar_comp: FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term =
  fun c  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (typ,u) ->
        let t = resugar_term typ in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_Tot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2871 = FStar_Options.print_universes () in
             if uu____2871
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_Tot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.GTotal (typ,u) ->
        let t = resugar_term typ in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2907 = FStar_Options.print_universes () in
             if uu____2907
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_GTot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.Comp c1 ->
        let result =
          let uu____2930 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2930, FStar_Parser_AST.Nothing) in
        let uu____2931 = FStar_Options.print_effect_args () in
        if uu____2931
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___203_2971 =
                match uu___203_2971 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3013 -> aux l tl1
                     | uu____3018 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3038  ->
                 match uu____3038 with
                 | (e,uu____3044) ->
                     let uu____3045 = resugar_term e in
                     (uu____3045, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___204_3059 =
            match uu___204_3059 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3079 = resugar_term e in
                       (uu____3079, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3082 -> aux l tl1) in
          let decrease = aux [] c1.FStar_Syntax_Syntax.flags in
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name),
                 (FStar_List.append (result :: decrease) args1)))
        else
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name), [result]))
and resugar_binder:
  FStar_Syntax_Syntax.binder -> FStar_Range.range -> FStar_Parser_AST.binder
  =
  fun b  ->
    fun r  ->
      let uu____3106 = b in
      match uu____3106 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3110 =
                 let uu____3111 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3111 in
               FStar_Parser_AST.mk_binder uu____3110 r
                 FStar_Parser_AST.Type_level None
           | uu____3112 ->
               let uu____3113 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3113
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3115 =
                    let uu____3116 =
                      let uu____3119 = bv_as_unique_ident x in
                      (uu____3119, e) in
                    FStar_Parser_AST.Annotated uu____3116 in
                  FStar_Parser_AST.mk_binder uu____3115 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3127 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3127 in
      let uu____3128 =
        let uu____3129 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3129.FStar_Syntax_Syntax.n in
      match uu____3128 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3135 = mk1 FStar_Parser_AST.PatWild in Some uu____3135
          else
            (let uu____3137 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3137
               (fun aq  ->
                  let uu____3143 =
                    let uu____3144 =
                      let uu____3145 =
                        let uu____3149 = bv_as_unique_ident x in
                        (uu____3149, aq) in
                      FStar_Parser_AST.PatVar uu____3145 in
                    mk1 uu____3144 in
                  Some uu____3143))
      | uu____3151 ->
          let uu____3152 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3152
            (fun aq  ->
               let pat =
                 let uu____3159 =
                   let uu____3160 =
                     let uu____3164 = bv_as_unique_ident x in
                     (uu____3164, aq) in
                   FStar_Parser_AST.PatVar uu____3160 in
                 mk1 uu____3159 in
               let uu____3166 = FStar_Options.print_bound_var_types () in
               if uu____3166
               then
                 let uu____3168 =
                   let uu____3169 =
                     let uu____3170 =
                       let uu____3173 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3173) in
                     FStar_Parser_AST.PatAscribed uu____3170 in
                   mk1 uu____3169 in
                 Some uu____3168
               else Some pat)
and resugar_pat: FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
    let rec aux p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
      | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
          mk1
            (FStar_Parser_AST.PatName
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          FStar_Ident.lid_equals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Syntax_Const.cons_lid
          ->
          let args1 =
            FStar_List.map
              (fun uu____3219  -> match uu____3219 with | (p2,b) -> aux p2)
              args in
          mk1 (FStar_Parser_AST.PatList args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          (FStar_Syntax_Util.is_tuple_data_lid'
             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
            ||
            (FStar_Syntax_Util.is_dtuple_data_lid'
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
          ->
          let args1 =
            FStar_List.map
              (fun uu____3248  -> match uu____3248 with | (p2,b) -> aux p2)
              args in
          let uu____3253 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3253
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3261;
             FStar_Syntax_Syntax.fv_delta = uu____3262;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3283 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3283 FStar_List.rev in
          let args1 =
            let uu____3292 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3302  ->
                      match uu____3302 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3292 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3344 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3344
            | (hd1::tl1,hd2::tl2) ->
                let uu____3358 = map21 tl1 tl2 in (hd1, hd2) :: uu____3358 in
          let args2 =
            let uu____3368 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3368 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3396  -> match uu____3396 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3407 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3407 with
           | Some (op,uu____3412) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3417 =
                 let uu____3418 =
                   let uu____3422 = bv_as_unique_ident v1 in
                   (uu____3422, None) in
                 FStar_Parser_AST.PatVar uu____3418 in
               mk1 uu____3417)
      | FStar_Syntax_Syntax.Pat_wild uu____3424 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3432 =
              let uu____3433 =
                let uu____3437 = bv_as_unique_ident bv in (uu____3437, None) in
              FStar_Parser_AST.PatVar uu____3433 in
            mk1 uu____3432 in
          let uu____3439 = FStar_Options.print_bound_var_types () in
          if uu____3439
          then
            let uu____3440 =
              let uu____3441 =
                let uu____3444 = resugar_term term in (pat, uu____3444) in
              FStar_Parser_AST.PatAscribed uu____3441 in
            mk1 uu____3440
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___205_3449  ->
    match uu___205_3449 with
    | FStar_Syntax_Syntax.Assumption  -> Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  -> Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  -> Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        Some FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        if true then None else Some FStar_Parser_AST.Visible
    | FStar_Syntax_Syntax.Irreducible  -> Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  -> Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  -> Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  -> Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  -> Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  -> Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  ->
        if true then None else Some FStar_Parser_AST.Logic
    | FStar_Syntax_Syntax.Reifiable  -> Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____3455 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3456 -> None
    | FStar_Syntax_Syntax.Projector uu____3457 -> None
    | FStar_Syntax_Syntax.RecordType uu____3460 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3465 -> None
    | FStar_Syntax_Syntax.Action uu____3470 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___206_3473  ->
    match uu___206_3473 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
let resugar_typ:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelts* FStar_Parser_AST.tycon)
  =
  fun datacon_ses  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tylid,uvs,bs,t,uu____3495,datacons) ->
          let uu____3501 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3512,uu____3513,uu____3514,inductive_lid,uu____3516,uu____3517)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3520 -> failwith "unexpected")) in
          (match uu____3501 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3531 = FStar_Options.print_implicits () in
                 if uu____3531 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3538 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___207_3540  ->
                           match uu___207_3540 with
                           | FStar_Syntax_Syntax.RecordType uu____3541 ->
                               true
                           | uu____3546 -> false)) in
                 if uu____3538
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3574,univs1,term,uu____3577,num,uu____3579)
                         ->
                         let uu____3582 =
                           let uu____3583 = FStar_Syntax_Subst.compress term in
                           uu____3583.FStar_Syntax_Syntax.n in
                         (match uu____3582 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3592) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3623  ->
                                        match uu____3623 with
                                        | (b,qual) ->
                                            let uu____3632 =
                                              let uu____3633 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3633 in
                                            let uu____3634 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3632, uu____3634, None))) in
                              FStar_List.append mfields fields
                          | uu____3640 -> failwith "unexpected")
                     | uu____3646 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3713,num,uu____3715) ->
                          let c =
                            let uu____3725 =
                              let uu____3727 = resugar_term term in
                              Some uu____3727 in
                            ((l.FStar_Ident.ident), uu____3725, None, false) in
                          c :: constructors
                      | uu____3736 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3775 ->
          failwith
            "Impossible : only Sig_inductive_typ can be resugared as types"
let mk_decl:
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____3789 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3789;
          FStar_Parser_AST.attrs = []
        }
let decl'_to_decl:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
let resugar_tscheme':
  Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun name  ->
    fun ts  ->
      let uu____3802 = ts in
      match uu____3802 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3808 =
            let uu____3809 =
              let uu____3816 =
                let uu____3821 =
                  let uu____3825 =
                    let uu____3826 =
                      let uu____3833 = resugar_term typ in
                      (name1, [], None, uu____3833) in
                    FStar_Parser_AST.TyconAbbrev uu____3826 in
                  (uu____3825, None) in
                [uu____3821] in
              (false, uu____3816) in
            FStar_Parser_AST.Tycon uu____3809 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3808
let resugar_tscheme: FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun ts  -> resugar_tscheme' "tsheme" ts
let resugar_eff_decl:
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let resugar_action d for_free1 =
            let action_params =
              FStar_Syntax_Subst.open_binders
                d.FStar_Syntax_Syntax.action_params in
            let uu____3872 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3872 with
            | (bs,action_defn) ->
                let uu____3877 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3877 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3883 = FStar_Options.print_implicits () in
                       if uu____3883
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3887 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3887 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3896 =
                           let uu____3902 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3902,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3896 in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un in
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2, None, t)), None)]))
                     else
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2, None, action_defn1)),
                                 None)]))) in
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident in
          let uu____3941 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____3941 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____3947 = FStar_Options.print_implicits () in
                if uu____3947 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____3951 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____3951 FStar_List.rev in
              let eff_typ1 = resugar_term eff_typ in
              let ret_wp =
                resugar_tscheme' "ret_wp" ed.FStar_Syntax_Syntax.ret_wp in
              let bind_wp =
                resugar_tscheme' "bind_wp" ed.FStar_Syntax_Syntax.ret_wp in
              let if_then_else1 =
                resugar_tscheme' "if_then_else"
                  ed.FStar_Syntax_Syntax.if_then_else in
              let ite_wp =
                resugar_tscheme' "ite_wp" ed.FStar_Syntax_Syntax.ite_wp in
              let stronger =
                resugar_tscheme' "stronger" ed.FStar_Syntax_Syntax.stronger in
              let close_wp =
                resugar_tscheme' "close_wp" ed.FStar_Syntax_Syntax.close_wp in
              let assert_p =
                resugar_tscheme' "assert_p" ed.FStar_Syntax_Syntax.assert_p in
              let assume_p =
                resugar_tscheme' "assume_p" ed.FStar_Syntax_Syntax.assume_p in
              let null_wp =
                resugar_tscheme' "null_wp" ed.FStar_Syntax_Syntax.null_wp in
              let trivial =
                resugar_tscheme' "trivial" ed.FStar_Syntax_Syntax.trivial in
              let repr =
                resugar_tscheme' "repr" ([], (ed.FStar_Syntax_Syntax.repr)) in
              let return_repr =
                resugar_tscheme' "return_repr"
                  ed.FStar_Syntax_Syntax.return_repr in
              let bind_repr =
                resugar_tscheme' "bind_repr" ed.FStar_Syntax_Syntax.bind_repr in
              let mandatory_members_decls =
                if for_free
                then [repr; return_repr; bind_repr]
                else
                  [repr;
                  return_repr;
                  bind_repr;
                  ret_wp;
                  bind_wp;
                  if_then_else1;
                  ite_wp;
                  stronger;
                  close_wp;
                  assert_p;
                  assume_p;
                  null_wp;
                  trivial] in
              let actions =
                FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                  (FStar_List.map (fun a  -> resugar_action a false)) in
              let decls = FStar_List.append mandatory_members_decls actions in
              mk_decl r q
                (FStar_Parser_AST.NewEffect
                   (FStar_Parser_AST.DefineEffect
                      (eff_name, eff_binders2, eff_typ1, decls)))
let resugar_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Parser_AST.decl option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3992) ->
        let uu____3997 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4008 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4017 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4021 -> false
                  | uu____4029 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____3997 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4049 se1 =
               match uu____4049 with
               | (datacon_ses1,tycons) ->
                   let uu____4064 = resugar_typ datacon_ses1 se1 in
                   (match uu____4064 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4073 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4073 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4092 =
                         let uu____4093 =
                           let uu____4094 =
                             let uu____4101 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4101) in
                           FStar_Parser_AST.Tycon uu____4094 in
                         decl'_to_decl se uu____4093 in
                       Some uu____4092
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4118,uu____4119,uu____4120,uu____4121,uu____4122)
                            ->
                            let uu____4125 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4125
                        | uu____4127 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4129 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4133,attrs) ->
        let uu____4139 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___208_4141  ->
                  match uu___208_4141 with
                  | FStar_Syntax_Syntax.Projector (uu____4142,uu____4143) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4144 -> true
                  | uu____4145 -> false)) in
        if uu____4139
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4170) ->
               let uu____4177 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4177
           | uu____4181 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4185 =
          let uu____4186 =
            let uu____4187 =
              let uu____4190 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4190) in
            FStar_Parser_AST.Assume uu____4187 in
          decl'_to_decl se uu____4186 in
        Some uu____4185
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4192 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4192
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4194 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4194
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4201,t) ->
              let uu____4208 = resugar_term t in Some uu____4208
          | uu____4209 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4214,t) ->
              let uu____4221 = resugar_term t in Some uu____4221
          | uu____4222 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4237 -> failwith "Should not happen hopefully" in
        let uu____4242 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4242
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4250 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4250 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4257 = FStar_Options.print_implicits () in
               if uu____4257 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4263 =
               let uu____4264 =
                 let uu____4265 =
                   let uu____4272 =
                     let uu____4277 =
                       let uu____4281 =
                         let uu____4282 =
                           let uu____4289 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4289) in
                         FStar_Parser_AST.TyconAbbrev uu____4282 in
                       (uu____4281, None) in
                     [uu____4277] in
                   (false, uu____4272) in
                 FStar_Parser_AST.Tycon uu____4265 in
               decl'_to_decl se uu____4264 in
             Some uu____4263)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4304 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4304
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4308 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___209_4310  ->
                  match uu___209_4310 with
                  | FStar_Syntax_Syntax.Projector (uu____4311,uu____4312) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4313 -> true
                  | uu____4314 -> false)) in
        if uu____4308
        then None
        else
          (let uu____4317 =
             let uu____4318 =
               let uu____4319 =
                 let uu____4322 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4322) in
               FStar_Parser_AST.Val uu____4319 in
             decl'_to_decl se uu____4318 in
           Some uu____4317)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4323 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4332 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4340 -> None