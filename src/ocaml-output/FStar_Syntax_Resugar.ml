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
       (fun uu___186_37  ->
          match uu___186_37 with
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
            let uu____158 =
              let uu____161 =
                let uu____162 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____162 in
              (uu____161, r) in
            FStar_Ident.mk_ident uu____158 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op: Prims.string -> (Prims.string* Prims.int) option =
  fun s  ->
    let name_of_op uu___187_175 =
      match uu___187_175 with
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
      | uu____213 -> None in
    match s with
    | "op_String_Assignment" -> Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" -> Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" -> Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" -> Some (".()", (Prims.parse_int "0"))
    | uu____227 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____233 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____233 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____240 ->
               let op =
                 let uu____243 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some (op,uu____260) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____243 in
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
      let uu____358 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (fst d))) in
      match uu____358 with
      | Some op -> Some ((snd op), (Prims.parse_int "0"))
      | uu____383 ->
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
                (let uu____426 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____426
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
    let uu____439 =
      let uu____440 = FStar_Syntax_Subst.compress t in
      uu____440.FStar_Syntax_Syntax.n in
    match uu____439 with
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
        let uu____468 = string_to_op s in
        (match uu____468 with | Some t1 -> Some t1 | uu____482 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____492 -> None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____498 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____502 -> true
    | uu____503 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____531 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____531 in
    let var a r =
      let uu____539 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____539 in
    let uu____540 =
      let uu____541 = FStar_Syntax_Subst.compress t in
      uu____541.FStar_Syntax_Syntax.n in
    match uu____540 with
    | FStar_Syntax_Syntax.Tm_delayed uu____544 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____567 = let uu____569 = bv_as_unique_ident x in [uu____569] in
          FStar_Ident.lid_of_ids uu____567 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____572 = let uu____574 = bv_as_unique_ident x in [uu____574] in
          FStar_Ident.lid_of_ids uu____572 in
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
          let uu____598 =
            let uu____599 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____599 in
          mk1 uu____598
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
             | uu____610 -> failwith "wrong projector format")
          else
            (let uu____613 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____614 =
                    let uu____615 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____615 in
                  let uu____616 = FStar_String.get s (Prims.parse_int "0") in
                  uu____614 <> uu____616) in
             if uu____613
             then
               let uu____617 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____617
             else
               (let uu____619 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____619))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____626 = FStar_Options.print_universes () in
        if uu____626
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____630 =
                   let uu____631 =
                     let uu____635 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____635, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____631 in
                 mk1 uu____630) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____638 = FStar_Syntax_Syntax.is_teff t in
        if uu____638
        then
          let uu____639 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____639
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____642 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____642
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____643 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____643
         | uu____644 ->
             let uu____645 = FStar_Options.print_universes () in
             if uu____645
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____656 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____656))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____659) ->
        let uu____682 = FStar_Syntax_Subst.open_term xs body in
        (match uu____682 with
         | (xs1,body1) ->
             let xs2 =
               let uu____688 = FStar_Options.print_implicits () in
               if uu____688 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____695  ->
                       match uu____695 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____715 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____715 with
         | (xs1,body1) ->
             let xs2 =
               let uu____721 = FStar_Options.print_implicits () in
               if uu____721 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____726 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____726 FStar_List.rev in
             let rec aux body3 uu___188_739 =
               match uu___188_739 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____752 =
          let uu____755 =
            let uu____756 = FStar_Syntax_Syntax.mk_binder x in [uu____756] in
          FStar_Syntax_Subst.open_term uu____755 phi in
        (match uu____752 with
         | (x1,phi1) ->
             let b =
               let uu____760 = FStar_List.hd x1 in
               resugar_binder uu____760 t.FStar_Syntax_Syntax.pos in
             let uu____763 =
               let uu____764 =
                 let uu____767 = resugar_term phi1 in (b, uu____767) in
               FStar_Parser_AST.Refine uu____764 in
             mk1 uu____763)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___189_797 =
          match uu___189_797 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____844 -> failwith "last of an empty list" in
        let rec last_two uu___190_868 =
          match uu___190_868 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____888::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____940::t1 -> last_two t1 in
        let rec last_three uu___191_968 =
          match uu___191_968 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____988::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1006::uu____1007::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1080::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1116  ->
                    match uu____1116 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1130 = FStar_Options.print_implicits () in
          if uu____1130 then args else filter_imp args in
        let uu____1139 = resugar_term_as_op e in
        (match uu____1139 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1145) ->
             (match args1 with
              | (fst1,uu____1149)::(snd1,uu____1151)::rest ->
                  let e1 =
                    let uu____1175 =
                      let uu____1176 =
                        let uu____1180 =
                          let uu____1182 = resugar_term fst1 in
                          let uu____1183 =
                            let uu____1185 = resugar_term snd1 in
                            [uu____1185] in
                          uu____1182 :: uu____1183 in
                        ((FStar_Ident.id_of_text "*"), uu____1180) in
                      FStar_Parser_AST.Op uu____1176 in
                    mk1 uu____1175 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1190  ->
                         match uu____1190 with
                         | (x,uu____1194) ->
                             let uu____1195 =
                               let uu____1196 =
                                 let uu____1200 =
                                   let uu____1202 =
                                     let uu____1204 = resugar_term x in
                                     [uu____1204] in
                                   e1 :: uu____1202 in
                                 ((FStar_Ident.id_of_text "*"), uu____1200) in
                               FStar_Parser_AST.Op uu____1196 in
                             mk1 uu____1195) e1 rest
              | uu____1206 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1212) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1234)::[] -> b
               | uu____1247 -> failwith "wrong arguments to dtuple" in
             let uu____1255 =
               let uu____1256 = FStar_Syntax_Subst.compress body in
               uu____1256.FStar_Syntax_Syntax.n in
             (match uu____1255 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1261) ->
                  let uu____1284 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1284 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1290 = FStar_Options.print_implicits () in
                         if uu____1290 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1298 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1309  ->
                            match uu____1309 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1317) -> resugar_as_app e args1
         | Some (ref_read,uu____1321) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1324 = FStar_List.hd args1 in
             (match uu____1324 with
              | (t1,uu____1334) ->
                  let uu____1339 =
                    let uu____1340 = FStar_Syntax_Subst.compress t1 in
                    uu____1340.FStar_Syntax_Syntax.n in
                  (match uu____1339 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1353 =
                         let uu____1354 =
                           let uu____1357 = resugar_term t1 in
                           (uu____1357, f) in
                         FStar_Parser_AST.Project uu____1354 in
                       mk1 uu____1353
                   | uu____1358 -> resugar_term t1))
         | Some ("try_with",uu____1359) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1375 =
               match new_args with
               | (a1,uu____1389)::(a2,uu____1391)::[] -> (a1, a2)
               | uu____1416 -> failwith "wrong arguments to try_with" in
             (match uu____1375 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1442 =
                      let uu____1443 = FStar_Syntax_Subst.compress term in
                      uu____1443.FStar_Syntax_Syntax.n in
                    match uu____1442 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1448) ->
                        let uu____1471 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1471 with | (x1,e2) -> e2)
                    | uu____1476 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1478 = decomp body in resugar_term uu____1478 in
                  let handler1 =
                    let uu____1480 = decomp handler in
                    resugar_term uu____1480 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1486,uu____1487,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1504,uu____1505,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1518 =
                          let uu____1519 =
                            let uu____1524 = resugar_body t11 in
                            (uu____1524, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1519 in
                        mk1 uu____1518
                    | uu____1526 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1559 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1575) -> resugar_as_app e args1
         | Some (op,uu____1579) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1630 -> (xs, pat, t1) in
             let resugar body =
               let uu____1638 =
                 let uu____1639 = FStar_Syntax_Subst.compress body in
                 uu____1639.FStar_Syntax_Syntax.n in
               match uu____1638 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1644) ->
                   let uu____1667 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1667 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1673 = FStar_Options.print_implicits () in
                          if uu____1673 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1679 =
                          let uu____1684 =
                            let uu____1685 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1685.FStar_Syntax_Syntax.n in
                          match uu____1684 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1725  ->
                                                 match uu____1725 with
                                                 | (e2,uu____1729) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1732) ->
                                    let uu____1733 =
                                      let uu____1735 =
                                        let uu____1736 = name s r in
                                        mk1 uu____1736 in
                                      [uu____1735] in
                                    [uu____1733]
                                | uu____1739 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1744 ->
                              let uu____1745 = resugar_term body2 in
                              ([], uu____1745) in
                        (match uu____1679 with
                         | (pats,body3) ->
                             let uu____1755 = uncurry xs3 pats body3 in
                             (match uu____1755 with
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
               | uu____1782 ->
                   if op = "forall"
                   then
                     let uu____1783 =
                       let uu____1784 =
                         let uu____1791 = resugar_term body in
                         ([], [[]], uu____1791) in
                       FStar_Parser_AST.QForall uu____1784 in
                     mk1 uu____1783
                   else
                     (let uu____1798 =
                        let uu____1799 =
                          let uu____1806 = resugar_term body in
                          ([], [[]], uu____1806) in
                        FStar_Parser_AST.QExists uu____1799 in
                      mk1 uu____1798) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1826)::[] -> resugar b
                | uu____1839 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1846) ->
             let uu____1849 = FStar_List.hd args1 in
             (match uu____1849 with | (e1,uu____1859) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1886  ->
                       match uu____1886 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1891 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1891 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1899 =
                         let uu____1900 =
                           let uu____1904 =
                             let uu____1906 = last1 args1 in
                             resugar uu____1906 in
                           (op1, uu____1904) in
                         FStar_Parser_AST.Op uu____1900 in
                       mk1 uu____1899
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1918 =
                         let uu____1919 =
                           let uu____1923 =
                             let uu____1925 = last_two args1 in
                             resugar uu____1925 in
                           (op1, uu____1923) in
                         FStar_Parser_AST.Op uu____1919 in
                       mk1 uu____1918
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1937 =
                         let uu____1938 =
                           let uu____1942 =
                             let uu____1944 = last_three args1 in
                             resugar uu____1944 in
                           (op1, uu____1942) in
                         FStar_Parser_AST.Op uu____1938 in
                       mk1 uu____1937
                   | uu____1949 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
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
          let uu____2590 =
            let uu____2591 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2591 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2590 in
        let uu____2592 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2592
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___192_2602 =
          match uu___192_2602 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2603 =
                let uu____2604 = FStar_Syntax_Subst.compress e in
                uu____2604.FStar_Syntax_Syntax.n in
              (match uu____2603 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2630 =
                       let uu____2631 = FStar_Syntax_Subst.compress h in
                       uu____2631.FStar_Syntax_Syntax.n in
                     match uu____2630 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2638 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2638, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2646 = aux h1 in
                         (match uu____2646 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2658 -> failwith "wrong Data_app head format" in
                   let uu____2662 = aux head1 in
                   (match uu____2662 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2677 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2677, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2686  ->
                               match uu____2686 with
                               | (t1,uu____2692) ->
                                   let uu____2693 = resugar_term t1 in
                                   (uu____2693, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2694 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2694
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2699 = FStar_Options.print_universes () in
                           if uu____2699
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2709,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2715,uu____2716) -> resugar_term e
                    | uu____2721 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2722 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2728,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2744 =
                      let uu____2745 =
                        let uu____2750 = resugar_seq t11 in
                        (uu____2750, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2745 in
                    mk1 uu____2744
                | uu____2752 -> t1 in
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
               | uu____2765 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2767 =
                let uu____2768 = FStar_Syntax_Subst.compress e in
                uu____2768.FStar_Syntax_Syntax.n in
              (match uu____2767 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2772;
                      FStar_Syntax_Syntax.pos = uu____2773;
                      FStar_Syntax_Syntax.vars = uu____2774;_},(term,uu____2776)::[])
                   -> resugar_term term
               | uu____2798 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2820  ->
                       match uu____2820 with
                       | (x,uu____2824) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2826,p) ->
             let uu____2828 =
               let uu____2829 =
                 let uu____2833 = resugar_term e in (uu____2833, l, p) in
               FStar_Parser_AST.Labeled uu____2829 in
             mk1 uu____2828
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2842 =
               let uu____2843 =
                 let uu____2848 = resugar_term e in
                 let uu____2849 =
                   let uu____2850 =
                     let uu____2851 =
                       let uu____2857 =
                         let uu____2861 =
                           let uu____2864 = resugar_term t1 in
                           (uu____2864, FStar_Parser_AST.Nothing) in
                         [uu____2861] in
                       (name1, uu____2857) in
                     FStar_Parser_AST.Construct uu____2851 in
                   mk1 uu____2850 in
                 (uu____2848, uu____2849, None) in
               FStar_Parser_AST.Ascribed uu____2843 in
             mk1 uu____2842
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2874,t1) ->
             let uu____2880 =
               let uu____2881 =
                 let uu____2886 = resugar_term e in
                 let uu____2887 =
                   let uu____2888 =
                     let uu____2889 =
                       let uu____2895 =
                         let uu____2899 =
                           let uu____2902 = resugar_term t1 in
                           (uu____2902, FStar_Parser_AST.Nothing) in
                         [uu____2899] in
                       (name1, uu____2895) in
                     FStar_Parser_AST.Construct uu____2889 in
                   mk1 uu____2888 in
                 (uu____2886, uu____2887, None) in
               FStar_Parser_AST.Ascribed uu____2881 in
             mk1 uu____2880)
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
             let uu____2933 = FStar_Options.print_universes () in
             if uu____2933
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
             let uu____2969 = FStar_Options.print_universes () in
             if uu____2969
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
          let uu____2992 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2992, FStar_Parser_AST.Nothing) in
        let uu____2993 = FStar_Options.print_effect_args () in
        if uu____2993
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___193_3033 =
                match uu___193_3033 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3075 -> aux l tl1
                     | uu____3080 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3100  ->
                 match uu____3100 with
                 | (e,uu____3106) ->
                     let uu____3107 = resugar_term e in
                     (uu____3107, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___194_3121 =
            match uu___194_3121 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3141 = resugar_term e in
                       (uu____3141, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3144 -> aux l tl1) in
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
      let uu____3168 = b in
      match uu____3168 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3172 =
                 let uu____3173 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3173 in
               FStar_Parser_AST.mk_binder uu____3172 r
                 FStar_Parser_AST.Type_level None
           | uu____3174 ->
               let uu____3175 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3175
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3177 =
                    let uu____3178 =
                      let uu____3181 = bv_as_unique_ident x in
                      (uu____3181, e) in
                    FStar_Parser_AST.Annotated uu____3178 in
                  FStar_Parser_AST.mk_binder uu____3177 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3189 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3189 in
      let uu____3190 =
        let uu____3191 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3191.FStar_Syntax_Syntax.n in
      match uu____3190 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3197 = mk1 FStar_Parser_AST.PatWild in Some uu____3197
          else
            (let uu____3199 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3199
               (fun aq  ->
                  let uu____3205 =
                    let uu____3206 =
                      let uu____3207 =
                        let uu____3211 = bv_as_unique_ident x in
                        (uu____3211, aq) in
                      FStar_Parser_AST.PatVar uu____3207 in
                    mk1 uu____3206 in
                  Some uu____3205))
      | uu____3213 ->
          let uu____3214 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3214
            (fun aq  ->
               let pat =
                 let uu____3221 =
                   let uu____3222 =
                     let uu____3226 = bv_as_unique_ident x in
                     (uu____3226, aq) in
                   FStar_Parser_AST.PatVar uu____3222 in
                 mk1 uu____3221 in
               let uu____3228 = FStar_Options.print_bound_var_types () in
               if uu____3228
               then
                 let uu____3230 =
                   let uu____3231 =
                     let uu____3232 =
                       let uu____3235 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3235) in
                     FStar_Parser_AST.PatAscribed uu____3232 in
                   mk1 uu____3231 in
                 Some uu____3230
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
              (fun uu____3281  -> match uu____3281 with | (p2,b) -> aux p2)
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
              (fun uu____3310  -> match uu____3310 with | (p2,b) -> aux p2)
              args in
          let uu____3315 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3315
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3323;
             FStar_Syntax_Syntax.fv_delta = uu____3324;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3345 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3345 FStar_List.rev in
          let args1 =
            let uu____3354 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3364  ->
                      match uu____3364 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3354 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3406 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3406
            | (hd1::tl1,hd2::tl2) ->
                let uu____3420 = map21 tl1 tl2 in (hd1, hd2) :: uu____3420 in
          let args2 =
            let uu____3430 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3430 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3458  -> match uu____3458 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3469 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3469 with
           | Some (op,uu____3474) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3479 =
                 let uu____3480 =
                   let uu____3484 = bv_as_unique_ident v1 in
                   (uu____3484, None) in
                 FStar_Parser_AST.PatVar uu____3480 in
               mk1 uu____3479)
      | FStar_Syntax_Syntax.Pat_wild uu____3486 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3494 =
              let uu____3495 =
                let uu____3499 = bv_as_unique_ident bv in (uu____3499, None) in
              FStar_Parser_AST.PatVar uu____3495 in
            mk1 uu____3494 in
          let uu____3501 = FStar_Options.print_bound_var_types () in
          if uu____3501
          then
            let uu____3502 =
              let uu____3503 =
                let uu____3506 = resugar_term term in (pat, uu____3506) in
              FStar_Parser_AST.PatAscribed uu____3503 in
            mk1 uu____3502
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___195_3511  ->
    match uu___195_3511 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3517 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3518 -> None
    | FStar_Syntax_Syntax.Projector uu____3519 -> None
    | FStar_Syntax_Syntax.RecordType uu____3522 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3527 -> None
    | FStar_Syntax_Syntax.Action uu____3532 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___196_3535  ->
    match uu___196_3535 with
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
          (tylid,uvs,bs,t,uu____3557,datacons) ->
          let uu____3563 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3574,uu____3575,uu____3576,inductive_lid,uu____3578,uu____3579)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3582 -> failwith "unexpected")) in
          (match uu____3563 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3593 = FStar_Options.print_implicits () in
                 if uu____3593 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3600 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___197_3602  ->
                           match uu___197_3602 with
                           | FStar_Syntax_Syntax.RecordType uu____3603 ->
                               true
                           | uu____3608 -> false)) in
                 if uu____3600
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3636,univs1,term,uu____3639,num,uu____3641)
                         ->
                         let uu____3644 =
                           let uu____3645 = FStar_Syntax_Subst.compress term in
                           uu____3645.FStar_Syntax_Syntax.n in
                         (match uu____3644 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3654) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3685  ->
                                        match uu____3685 with
                                        | (b,qual) ->
                                            let uu____3694 =
                                              let uu____3695 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3695 in
                                            let uu____3696 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3694, uu____3696, None))) in
                              FStar_List.append mfields fields
                          | uu____3702 -> failwith "unexpected")
                     | uu____3708 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3775,num,uu____3777) ->
                          let c =
                            let uu____3787 =
                              let uu____3789 = resugar_term term in
                              Some uu____3789 in
                            ((l.FStar_Ident.ident), uu____3787, None, false) in
                          c :: constructors
                      | uu____3798 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3837 ->
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
        let uu____3851 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3851;
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
      let uu____3864 = ts in
      match uu____3864 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3870 =
            let uu____3871 =
              let uu____3878 =
                let uu____3883 =
                  let uu____3887 =
                    let uu____3888 =
                      let uu____3895 = resugar_term typ in
                      (name1, [], None, uu____3895) in
                    FStar_Parser_AST.TyconAbbrev uu____3888 in
                  (uu____3887, None) in
                [uu____3883] in
              (false, uu____3878) in
            FStar_Parser_AST.Tycon uu____3871 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3870
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
            let uu____3934 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3934 with
            | (bs,action_defn) ->
                let uu____3939 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3939 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3945 = FStar_Options.print_implicits () in
                       if uu____3945
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3949 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3949 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3958 =
                           let uu____3964 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3964,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3958 in
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
          let uu____4003 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4003 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4009 = FStar_Options.print_implicits () in
                if uu____4009 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4013 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4013 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4054) ->
        let uu____4059 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4070 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4079 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4083 -> false
                  | uu____4091 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4059 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4111 se1 =
               match uu____4111 with
               | (datacon_ses1,tycons) ->
                   let uu____4126 = resugar_typ datacon_ses1 se1 in
                   (match uu____4126 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4135 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4135 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4154 =
                         let uu____4155 =
                           let uu____4156 =
                             let uu____4163 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4163) in
                           FStar_Parser_AST.Tycon uu____4156 in
                         decl'_to_decl se uu____4155 in
                       Some uu____4154
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4180,uu____4181,uu____4182,uu____4183,uu____4184)
                            ->
                            let uu____4187 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4187
                        | uu____4189 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4191 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4195,attrs) ->
        let uu____4201 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___198_4203  ->
                  match uu___198_4203 with
                  | FStar_Syntax_Syntax.Projector (uu____4204,uu____4205) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4206 -> true
                  | uu____4207 -> false)) in
        if uu____4201
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4232) ->
               let uu____4239 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4239
           | uu____4243 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4246,fml) ->
        let uu____4248 =
          let uu____4249 =
            let uu____4250 =
              let uu____4253 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4253) in
            FStar_Parser_AST.Assume uu____4250 in
          decl'_to_decl se uu____4249 in
        Some uu____4248
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4255 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4255
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4257 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4257
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4264,t) ->
              let uu____4271 = resugar_term t in Some uu____4271
          | uu____4272 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4277,t) ->
              let uu____4284 = resugar_term t in Some uu____4284
          | uu____4285 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4300 -> failwith "Should not happen hopefully" in
        let uu____4305 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4305
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4313 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4313 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4320 = FStar_Options.print_implicits () in
               if uu____4320 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4326 =
               let uu____4327 =
                 let uu____4328 =
                   let uu____4335 =
                     let uu____4340 =
                       let uu____4344 =
                         let uu____4345 =
                           let uu____4352 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4352) in
                         FStar_Parser_AST.TyconAbbrev uu____4345 in
                       (uu____4344, None) in
                     [uu____4340] in
                   (false, uu____4335) in
                 FStar_Parser_AST.Tycon uu____4328 in
               decl'_to_decl se uu____4327 in
             Some uu____4326)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4367 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4367
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4371 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___199_4373  ->
                  match uu___199_4373 with
                  | FStar_Syntax_Syntax.Projector (uu____4374,uu____4375) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4376 -> true
                  | uu____4377 -> false)) in
        if uu____4371
        then None
        else
          (let uu____4380 =
             let uu____4381 =
               let uu____4382 =
                 let uu____4385 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4385) in
               FStar_Parser_AST.Val uu____4382 in
             decl'_to_decl se uu____4381 in
           Some uu____4380)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4386 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4395 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4403 -> None