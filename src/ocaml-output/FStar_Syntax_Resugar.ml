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
       (fun uu___183_37  ->
          match uu___183_37 with
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
    let name_of_op uu___184_173 =
      match uu___184_173 with
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
          let uu____565 = let uu____567 = bv_as_unique_ident x in [uu____567] in
          FStar_Ident.lid_of_ids uu____565 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____570 = let uu____572 = bv_as_unique_ident x in [uu____572] in
          FStar_Ident.lid_of_ids uu____570 in
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
          let uu____596 =
            let uu____597 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____597 in
          mk1 uu____596
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
             | uu____608 -> failwith "wrong projector format")
          else
            (let uu____611 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____612 =
                    let uu____613 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____613 in
                  let uu____614 = FStar_String.get s (Prims.parse_int "0") in
                  uu____612 <> uu____614) in
             if uu____611
             then
               let uu____615 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____615
             else
               (let uu____617 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____617))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____624 = FStar_Options.print_universes () in
        if uu____624
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____628 =
                   let uu____629 =
                     let uu____633 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____633, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____629 in
                 mk1 uu____628) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____636 = FStar_Syntax_Syntax.is_teff t in
        if uu____636
        then
          let uu____637 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____637
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____640 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____640
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____641 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____641
         | uu____642 ->
             let uu____643 = FStar_Options.print_universes () in
             if uu____643
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____654 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____654))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____657) ->
        let uu____680 = FStar_Syntax_Subst.open_term xs body in
        (match uu____680 with
         | (xs1,body1) ->
             let xs2 =
               let uu____686 = FStar_Options.print_implicits () in
               if uu____686 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____693  ->
                       match uu____693 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____713 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____713 with
         | (xs1,body1) ->
             let xs2 =
               let uu____719 = FStar_Options.print_implicits () in
               if uu____719 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____724 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____724 FStar_List.rev in
             let rec aux body3 uu___185_737 =
               match uu___185_737 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____750 =
          let uu____753 =
            let uu____754 = FStar_Syntax_Syntax.mk_binder x in [uu____754] in
          FStar_Syntax_Subst.open_term uu____753 phi in
        (match uu____750 with
         | (x1,phi1) ->
             let b =
               let uu____758 = FStar_List.hd x1 in
               resugar_binder uu____758 t.FStar_Syntax_Syntax.pos in
             let uu____761 =
               let uu____762 =
                 let uu____765 = resugar_term phi1 in (b, uu____765) in
               FStar_Parser_AST.Refine uu____762 in
             mk1 uu____761)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___186_795 =
          match uu___186_795 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____842 -> failwith "last of an empty list" in
        let rec last_two uu___187_866 =
          match uu___187_866 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____886::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____938::t1 -> last_two t1 in
        let rec last_three uu___188_966 =
          match uu___188_966 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____986::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1004::uu____1005::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1078::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1114  ->
                    match uu____1114 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1128 = FStar_Options.print_implicits () in
          if uu____1128 then args else filter_imp args in
        let uu____1137 = resugar_term_as_op e in
        (match uu____1137 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1143) ->
             (match args1 with
              | (fst1,uu____1147)::(snd1,uu____1149)::rest ->
                  let e1 =
                    let uu____1173 =
                      let uu____1174 =
                        let uu____1178 =
                          let uu____1180 = resugar_term fst1 in
                          let uu____1181 =
                            let uu____1183 = resugar_term snd1 in
                            [uu____1183] in
                          uu____1180 :: uu____1181 in
                        ((FStar_Ident.id_of_text "*"), uu____1178) in
                      FStar_Parser_AST.Op uu____1174 in
                    mk1 uu____1173 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1188  ->
                         match uu____1188 with
                         | (x,uu____1192) ->
                             let uu____1193 =
                               let uu____1194 =
                                 let uu____1198 =
                                   let uu____1200 =
                                     let uu____1202 = resugar_term x in
                                     [uu____1202] in
                                   e1 :: uu____1200 in
                                 ((FStar_Ident.id_of_text "*"), uu____1198) in
                               FStar_Parser_AST.Op uu____1194 in
                             mk1 uu____1193) e1 rest
              | uu____1204 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1210) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1232)::[] -> b
               | uu____1245 -> failwith "wrong arguments to dtuple" in
             let uu____1253 =
               let uu____1254 = FStar_Syntax_Subst.compress body in
               uu____1254.FStar_Syntax_Syntax.n in
             (match uu____1253 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1259) ->
                  let uu____1282 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1282 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1288 = FStar_Options.print_implicits () in
                         if uu____1288 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1296 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1307  ->
                            match uu____1307 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1315) -> resugar_as_app e args1
         | Some (ref_read,uu____1319) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1322 = FStar_List.hd args1 in
             (match uu____1322 with
              | (t1,uu____1332) ->
                  let uu____1337 =
                    let uu____1338 = FStar_Syntax_Subst.compress t1 in
                    uu____1338.FStar_Syntax_Syntax.n in
                  (match uu____1337 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1351 =
                         let uu____1352 =
                           let uu____1355 = resugar_term t1 in
                           (uu____1355, f) in
                         FStar_Parser_AST.Project uu____1352 in
                       mk1 uu____1351
                   | uu____1356 -> resugar_term t1))
         | Some ("try_with",uu____1357) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1373 =
               match new_args with
               | (a1,uu____1387)::(a2,uu____1389)::[] -> (a1, a2)
               | uu____1414 -> failwith "wrong arguments to try_with" in
             (match uu____1373 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1440 =
                      let uu____1441 = FStar_Syntax_Subst.compress term in
                      uu____1441.FStar_Syntax_Syntax.n in
                    match uu____1440 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1446) ->
                        let uu____1469 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1469 with | (x1,e2) -> e2)
                    | uu____1474 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1476 = decomp body in resugar_term uu____1476 in
                  let handler1 =
                    let uu____1478 = decomp handler in
                    resugar_term uu____1478 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1484,uu____1485,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1502,uu____1503,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1516 =
                          let uu____1517 =
                            let uu____1522 = resugar_body t11 in
                            (uu____1522, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1517 in
                        mk1 uu____1516
                    | uu____1524 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1557 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1573) -> resugar_as_app e args1
         | Some (op,uu____1577) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1628 -> (xs, pat, t1) in
             let resugar body =
               let uu____1636 =
                 let uu____1637 = FStar_Syntax_Subst.compress body in
                 uu____1637.FStar_Syntax_Syntax.n in
               match uu____1636 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1642) ->
                   let uu____1665 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1665 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1671 = FStar_Options.print_implicits () in
                          if uu____1671 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1677 =
                          let uu____1682 =
                            let uu____1683 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1683.FStar_Syntax_Syntax.n in
                          match uu____1682 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1723  ->
                                                 match uu____1723 with
                                                 | (e2,uu____1727) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1730) ->
                                    let uu____1731 =
                                      let uu____1733 =
                                        let uu____1734 = name s r in
                                        mk1 uu____1734 in
                                      [uu____1733] in
                                    [uu____1731]
                                | uu____1737 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1742 ->
                              let uu____1743 = resugar_term body2 in
                              ([], uu____1743) in
                        (match uu____1677 with
                         | (pats,body3) ->
                             let uu____1753 = uncurry xs3 pats body3 in
                             (match uu____1753 with
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
               | uu____1780 ->
                   if op = "forall"
                   then
                     let uu____1781 =
                       let uu____1782 =
                         let uu____1789 = resugar_term body in
                         ([], [[]], uu____1789) in
                       FStar_Parser_AST.QForall uu____1782 in
                     mk1 uu____1781
                   else
                     (let uu____1796 =
                        let uu____1797 =
                          let uu____1804 = resugar_term body in
                          ([], [[]], uu____1804) in
                        FStar_Parser_AST.QExists uu____1797 in
                      mk1 uu____1796) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1824)::[] -> resugar b
                | uu____1837 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1844) ->
             let uu____1847 = FStar_List.hd args1 in
             (match uu____1847 with | (e1,uu____1857) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1884  ->
                       match uu____1884 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | x when x = (Prims.parse_int "0") ->
                  let uu____1890 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1890 with
                   | _0_27 when
                       (_0_27 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1898 =
                         let uu____1899 =
                           let uu____1903 =
                             let uu____1905 = last1 args1 in
                             resugar uu____1905 in
                           (op1, uu____1903) in
                         FStar_Parser_AST.Op uu____1899 in
                       mk1 uu____1898
                   | _0_28 when
                       (_0_28 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1917 =
                         let uu____1918 =
                           let uu____1922 =
                             let uu____1924 = last_two args1 in
                             resugar uu____1924 in
                           (op1, uu____1922) in
                         FStar_Parser_AST.Op uu____1918 in
                       mk1 uu____1917
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1936 =
                         let uu____1937 =
                           let uu____1941 =
                             let uu____1943 = last_three args1 in
                             resugar uu____1943 in
                           (op1, uu____1941) in
                         FStar_Parser_AST.Op uu____1937 in
                       mk1 uu____1936
                   | uu____1948 -> resugar_as_app e args1)
              | x when
                  (x = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1957 =
                    let uu____1958 =
                      let uu____1962 =
                        let uu____1964 = last_two args1 in resugar uu____1964 in
                      (op1, uu____1962) in
                    FStar_Parser_AST.Op uu____1958 in
                  mk1 uu____1957
              | uu____1969 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1972,t1)::[]) ->
        let bnds =
          let uu____2027 =
            let uu____2030 = resugar_pat pat in
            let uu____2031 = resugar_term e in (uu____2030, uu____2031) in
          [uu____2027] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2042,t1)::(pat2,uu____2045,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2120 =
          let uu____2121 =
            let uu____2125 = resugar_term e in
            let uu____2126 = resugar_term t1 in
            let uu____2127 = resugar_term t2 in
            (uu____2125, uu____2126, uu____2127) in
          FStar_Parser_AST.If uu____2121 in
        mk1 uu____2120
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2167 =
          match uu____2167 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2186 = resugar_term e1 in Some uu____2186 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2189 =
          let uu____2190 =
            let uu____2198 = resugar_term e in
            let uu____2199 = FStar_List.map resugar_branch branches in
            (uu____2198, uu____2199) in
          FStar_Parser_AST.Match uu____2190 in
        mk1 uu____2189
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2221) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2274 =
          let uu____2275 =
            let uu____2280 = resugar_term e in (uu____2280, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2275 in
        mk1 uu____2274
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2298 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2298 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2314 =
                 let uu____2317 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2317 in
               match uu____2314 with
               | (univs1,td) ->
                   let uu____2324 =
                     let uu____2331 =
                       let uu____2332 = FStar_Syntax_Subst.compress td in
                       uu____2332.FStar_Syntax_Syntax.n in
                     match uu____2331 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2341,(t1,uu____2343)::(d,uu____2345)::[]) ->
                         (t1, d)
                     | uu____2379 -> failwith "wrong let binding format" in
                   (match uu____2324 with
                    | (typ,def) ->
                        let uu____2400 =
                          let uu____2404 =
                            let uu____2405 = FStar_Syntax_Subst.compress def in
                            uu____2405.FStar_Syntax_Syntax.n in
                          match uu____2404 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2413) ->
                              let uu____2436 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2436 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2445 =
                                       FStar_Options.print_implicits () in
                                     if uu____2445 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2447 -> ([], def, false) in
                        (match uu____2400 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2468 =
                                 FStar_Options.print_universes () in
                               if uu____2468
                               then
                                 let uu____2469 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2469
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2474 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2485 =
                                     let uu____2486 =
                                       let uu____2487 =
                                         let uu____2491 =
                                           bv_as_unique_ident bv in
                                         (uu____2491, None) in
                                       FStar_Parser_AST.PatVar uu____2487 in
                                     mk_pat uu____2486 in
                                   (uu____2485, term) in
                             (match uu____2474 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2508  ->
                                              match uu____2508 with
                                              | (bv,uu____2512) ->
                                                  let uu____2513 =
                                                    let uu____2514 =
                                                      let uu____2518 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2518, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2514 in
                                                  mk_pat uu____2513)) in
                                    let uu____2520 =
                                      let uu____2523 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2523) in
                                    let uu____2525 =
                                      universe_to_string univs1 in
                                    (uu____2520, uu____2525)
                                  else
                                    (let uu____2529 =
                                       let uu____2532 = resugar_term term1 in
                                       (pat, uu____2532) in
                                     let uu____2533 =
                                       universe_to_string univs1 in
                                     (uu____2529, uu____2533))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2572) ->
        let s =
          let uu____2586 =
            let uu____2587 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2587 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2586 in
        let uu____2591 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2591
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___189_2601 =
          match uu___189_2601 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2602 =
                let uu____2603 = FStar_Syntax_Subst.compress e in
                uu____2603.FStar_Syntax_Syntax.n in
              (match uu____2602 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2629 =
                       let uu____2630 = FStar_Syntax_Subst.compress h in
                       uu____2630.FStar_Syntax_Syntax.n in
                     match uu____2629 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2637 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2637, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2645 = aux h1 in
                         (match uu____2645 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2657 -> failwith "wrong Data_app head format" in
                   let uu____2661 = aux head1 in
                   (match uu____2661 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2676 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2676, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2685  ->
                               match uu____2685 with
                               | (t1,uu____2691) ->
                                   let uu____2692 = resugar_term t1 in
                                   (uu____2692, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2693 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2693
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2698 = FStar_Options.print_universes () in
                           if uu____2698
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2708,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2714,uu____2715) -> resugar_term e
                    | uu____2720 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2721 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2727,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2743 =
                      let uu____2744 =
                        let uu____2749 = resugar_seq t11 in
                        (uu____2749, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2744 in
                    mk1 uu____2743
                | uu____2751 -> t1 in
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
               | uu____2764 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2766 =
                let uu____2767 = FStar_Syntax_Subst.compress e in
                uu____2767.FStar_Syntax_Syntax.n in
              (match uu____2766 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2771;
                      FStar_Syntax_Syntax.pos = uu____2772;
                      FStar_Syntax_Syntax.vars = uu____2773;_},(term,uu____2775)::[])
                   -> resugar_term term
               | uu____2797 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2819  ->
                       match uu____2819 with
                       | (x,uu____2823) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2825,p) ->
             let uu____2827 =
               let uu____2828 =
                 let uu____2832 = resugar_term e in (uu____2832, l, p) in
               FStar_Parser_AST.Labeled uu____2828 in
             mk1 uu____2827
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2841 =
               let uu____2842 =
                 let uu____2847 = resugar_term e in
                 let uu____2848 =
                   let uu____2849 =
                     let uu____2850 =
                       let uu____2856 =
                         let uu____2860 =
                           let uu____2863 = resugar_term t1 in
                           (uu____2863, FStar_Parser_AST.Nothing) in
                         [uu____2860] in
                       (name1, uu____2856) in
                     FStar_Parser_AST.Construct uu____2850 in
                   mk1 uu____2849 in
                 (uu____2847, uu____2848, None) in
               FStar_Parser_AST.Ascribed uu____2842 in
             mk1 uu____2841
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2873,t1) ->
             let uu____2879 =
               let uu____2880 =
                 let uu____2885 = resugar_term e in
                 let uu____2886 =
                   let uu____2887 =
                     let uu____2888 =
                       let uu____2894 =
                         let uu____2898 =
                           let uu____2901 = resugar_term t1 in
                           (uu____2901, FStar_Parser_AST.Nothing) in
                         [uu____2898] in
                       (name1, uu____2894) in
                     FStar_Parser_AST.Construct uu____2888 in
                   mk1 uu____2887 in
                 (uu____2885, uu____2886, None) in
               FStar_Parser_AST.Ascribed uu____2880 in
             mk1 uu____2879)
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
             let uu____2932 = FStar_Options.print_universes () in
             if uu____2932
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
             let uu____2968 = FStar_Options.print_universes () in
             if uu____2968
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
          let uu____2991 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2991, FStar_Parser_AST.Nothing) in
        let uu____2992 = FStar_Options.print_effect_args () in
        if uu____2992
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___190_3032 =
                match uu___190_3032 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3074 -> aux l tl1
                     | uu____3079 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3099  ->
                 match uu____3099 with
                 | (e,uu____3105) ->
                     let uu____3106 = resugar_term e in
                     (uu____3106, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___191_3120 =
            match uu___191_3120 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3140 = resugar_term e in
                       (uu____3140, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3143 -> aux l tl1) in
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
      let uu____3167 = b in
      match uu____3167 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3171 =
                 let uu____3172 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3172 in
               FStar_Parser_AST.mk_binder uu____3171 r
                 FStar_Parser_AST.Type_level None
           | uu____3173 ->
               let uu____3174 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3174
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3176 =
                    let uu____3177 =
                      let uu____3180 = bv_as_unique_ident x in
                      (uu____3180, e) in
                    FStar_Parser_AST.Annotated uu____3177 in
                  FStar_Parser_AST.mk_binder uu____3176 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3188 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3188 in
      let uu____3189 =
        let uu____3190 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3190.FStar_Syntax_Syntax.n in
      match uu____3189 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3196 = mk1 FStar_Parser_AST.PatWild in Some uu____3196
          else
            (let uu____3198 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3198
               (fun aq  ->
                  let uu____3204 =
                    let uu____3205 =
                      let uu____3206 =
                        let uu____3210 = bv_as_unique_ident x in
                        (uu____3210, aq) in
                      FStar_Parser_AST.PatVar uu____3206 in
                    mk1 uu____3205 in
                  Some uu____3204))
      | uu____3212 ->
          let uu____3213 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3213
            (fun aq  ->
               let pat =
                 let uu____3220 =
                   let uu____3221 =
                     let uu____3225 = bv_as_unique_ident x in
                     (uu____3225, aq) in
                   FStar_Parser_AST.PatVar uu____3221 in
                 mk1 uu____3220 in
               let uu____3227 = FStar_Options.print_bound_var_types () in
               if uu____3227
               then
                 let uu____3229 =
                   let uu____3230 =
                     let uu____3231 =
                       let uu____3234 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3234) in
                     FStar_Parser_AST.PatAscribed uu____3231 in
                   mk1 uu____3230 in
                 Some uu____3229
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
              (fun uu____3280  -> match uu____3280 with | (p2,b) -> aux p2)
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
              (fun uu____3309  -> match uu____3309 with | (p2,b) -> aux p2)
              args in
          let uu____3314 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3314
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3322;
             FStar_Syntax_Syntax.fv_delta = uu____3323;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3344 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3344 FStar_List.rev in
          let args1 =
            let uu____3353 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3363  ->
                      match uu____3363 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3353 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3405 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3405
            | (hd1::tl1,hd2::tl2) ->
                let uu____3419 = map21 tl1 tl2 in (hd1, hd2) :: uu____3419 in
          let args2 =
            let uu____3429 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3429 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3457  -> match uu____3457 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3468 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3468 with
           | Some (op,uu____3473) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3478 =
                 let uu____3479 =
                   let uu____3483 = bv_as_unique_ident v1 in
                   (uu____3483, None) in
                 FStar_Parser_AST.PatVar uu____3479 in
               mk1 uu____3478)
      | FStar_Syntax_Syntax.Pat_wild uu____3485 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3493 =
              let uu____3494 =
                let uu____3498 = bv_as_unique_ident bv in (uu____3498, None) in
              FStar_Parser_AST.PatVar uu____3494 in
            mk1 uu____3493 in
          let uu____3500 = FStar_Options.print_bound_var_types () in
          if uu____3500
          then
            let uu____3501 =
              let uu____3502 =
                let uu____3505 = resugar_term term in (pat, uu____3505) in
              FStar_Parser_AST.PatAscribed uu____3502 in
            mk1 uu____3501
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___192_3510  ->
    match uu___192_3510 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3516 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3517 -> None
    | FStar_Syntax_Syntax.Projector uu____3518 -> None
    | FStar_Syntax_Syntax.RecordType uu____3521 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3526 -> None
    | FStar_Syntax_Syntax.Action uu____3531 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___193_3534  ->
    match uu___193_3534 with
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
          (tylid,uvs,bs,t,uu____3556,datacons) ->
          let uu____3562 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3573,uu____3574,uu____3575,inductive_lid,uu____3577,uu____3578)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3581 -> failwith "unexpected")) in
          (match uu____3562 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3592 = FStar_Options.print_implicits () in
                 if uu____3592 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3599 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___194_3601  ->
                           match uu___194_3601 with
                           | FStar_Syntax_Syntax.RecordType uu____3602 ->
                               true
                           | uu____3607 -> false)) in
                 if uu____3599
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3635,univs1,term,uu____3638,num,uu____3640)
                         ->
                         let uu____3643 =
                           let uu____3644 = FStar_Syntax_Subst.compress term in
                           uu____3644.FStar_Syntax_Syntax.n in
                         (match uu____3643 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3653) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3684  ->
                                        match uu____3684 with
                                        | (b,qual) ->
                                            let uu____3693 =
                                              let uu____3694 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3694 in
                                            let uu____3695 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3693, uu____3695, None))) in
                              FStar_List.append mfields fields
                          | uu____3701 -> failwith "unexpected")
                     | uu____3707 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3774,num,uu____3776) ->
                          let c =
                            let uu____3786 =
                              let uu____3788 = resugar_term term in
                              Some uu____3788 in
                            ((l.FStar_Ident.ident), uu____3786, None, false) in
                          c :: constructors
                      | uu____3797 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3836 ->
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
        let uu____3850 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3850;
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
      let uu____3863 = ts in
      match uu____3863 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3869 =
            let uu____3870 =
              let uu____3877 =
                let uu____3882 =
                  let uu____3886 =
                    let uu____3887 =
                      let uu____3894 = resugar_term typ in
                      (name1, [], None, uu____3894) in
                    FStar_Parser_AST.TyconAbbrev uu____3887 in
                  (uu____3886, None) in
                [uu____3882] in
              (false, uu____3877) in
            FStar_Parser_AST.Tycon uu____3870 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3869
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
            let uu____3933 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3933 with
            | (bs,action_defn) ->
                let uu____3938 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3938 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3944 = FStar_Options.print_implicits () in
                       if uu____3944
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3948 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3948 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3957 =
                           let uu____3963 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3963,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3957 in
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
          let uu____4002 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4002 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4008 = FStar_Options.print_implicits () in
                if uu____4008 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4012 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4012 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4053) ->
        let uu____4058 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4069 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4078 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4082 -> false
                  | uu____4090 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4058 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4110 se1 =
               match uu____4110 with
               | (datacon_ses1,tycons) ->
                   let uu____4125 = resugar_typ datacon_ses1 se1 in
                   (match uu____4125 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4134 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4134 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4153 =
                         let uu____4154 =
                           let uu____4155 =
                             let uu____4162 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4162) in
                           FStar_Parser_AST.Tycon uu____4155 in
                         decl'_to_decl se uu____4154 in
                       Some uu____4153
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4179,uu____4180,uu____4181,uu____4182,uu____4183)
                            ->
                            let uu____4186 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4186
                        | uu____4188 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4190 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4194,attrs) ->
        let uu____4200 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___195_4202  ->
                  match uu___195_4202 with
                  | FStar_Syntax_Syntax.Projector (uu____4203,uu____4204) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4205 -> true
                  | uu____4206 -> false)) in
        if uu____4200
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4231) ->
               let uu____4238 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4238
           | uu____4242 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4246 =
          let uu____4247 =
            let uu____4248 =
              let uu____4251 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4251) in
            FStar_Parser_AST.Assume uu____4248 in
          decl'_to_decl se uu____4247 in
        Some uu____4246
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4253 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4253
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4255 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4255
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4262,t) ->
              let uu____4269 = resugar_term t in Some uu____4269
          | uu____4270 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4275,t) ->
              let uu____4282 = resugar_term t in Some uu____4282
          | uu____4283 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4298 -> failwith "Should not happen hopefully" in
        let uu____4303 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4303
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4311 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4311 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4318 = FStar_Options.print_implicits () in
               if uu____4318 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4324 =
               let uu____4325 =
                 let uu____4326 =
                   let uu____4333 =
                     let uu____4338 =
                       let uu____4342 =
                         let uu____4343 =
                           let uu____4350 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4350) in
                         FStar_Parser_AST.TyconAbbrev uu____4343 in
                       (uu____4342, None) in
                     [uu____4338] in
                   (false, uu____4333) in
                 FStar_Parser_AST.Tycon uu____4326 in
               decl'_to_decl se uu____4325 in
             Some uu____4324)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4365 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4365
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4369 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_4371  ->
                  match uu___196_4371 with
                  | FStar_Syntax_Syntax.Projector (uu____4372,uu____4373) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4374 -> true
                  | uu____4375 -> false)) in
        if uu____4369
        then None
        else
          (let uu____4378 =
             let uu____4379 =
               let uu____4380 =
                 let uu____4383 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4383) in
               FStar_Parser_AST.Val uu____4380 in
             decl'_to_decl se uu____4379 in
           Some uu____4378)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4384 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4393 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4401 -> None