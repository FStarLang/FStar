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
       (fun uu___198_37  ->
          match uu___198_37 with
          | (uu____41,Some (FStar_Syntax_Syntax.Implicit uu____42)) -> false
          | uu____44 -> true))
let resugar_arg_qual:
  FStar_Syntax_Syntax.arg_qualifier Prims.option ->
    FStar_Parser_AST.arg_qualifier Prims.option Prims.option
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
let string_to_op: Prims.string -> (Prims.string* Prims.int) Prims.option =
  fun s  ->
    let name_of_op uu___199_173 =
      match uu___199_173 with
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
  FStar_Syntax_Syntax.term -> (Prims.string* Prims.int) Prims.option =
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
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (Prims.fst d))) in
      match uu____356 with
      | Some op -> Some ((Prims.snd op), (Prims.parse_int "0"))
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
let is_disj_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____505 -> true
    | uu____509 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____537 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____537 in
    let var a r =
      let uu____545 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____545 in
    let uu____546 =
      let uu____547 = FStar_Syntax_Subst.compress t in
      uu____547.FStar_Syntax_Syntax.n in
    match uu____546 with
    | FStar_Syntax_Syntax.Tm_delayed uu____550 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____573 = let uu____575 = bv_as_unique_ident x in [uu____575] in
          FStar_Ident.lid_of_ids uu____573 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____578 = let uu____580 = bv_as_unique_ident x in [uu____580] in
          FStar_Ident.lid_of_ids uu____578 in
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
          let uu____604 =
            let uu____605 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____605 in
          mk1 uu____604
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
             | uu____616 -> failwith "wrong projector format")
          else
            (let uu____619 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____620 =
                    let uu____621 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____621 in
                  let uu____622 = FStar_String.get s (Prims.parse_int "0") in
                  uu____620 <> uu____622) in
             if uu____619
             then
               let uu____623 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____623
             else
               (let uu____625 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____625))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____632 = FStar_Options.print_universes () in
        if uu____632
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____636 =
                   let uu____637 =
                     let uu____641 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____641, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____637 in
                 mk1 uu____636) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____644 = FStar_Syntax_Syntax.is_teff t in
        if uu____644
        then
          let uu____645 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____645
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____648 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____648
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____649 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____649
         | uu____650 ->
             let uu____651 = FStar_Options.print_universes () in
             if uu____651
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____662 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____662))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____665) ->
        let uu____688 = FStar_Syntax_Subst.open_term xs body in
        (match uu____688 with
         | (xs1,body1) ->
             let xs2 =
               let uu____694 = FStar_Options.print_implicits () in
               if uu____694 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____701  ->
                       match uu____701 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____721 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____721 with
         | (xs1,body1) ->
             let xs2 =
               let uu____727 = FStar_Options.print_implicits () in
               if uu____727 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____732 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun uu____737  ->
                         match uu____737 with
                         | (b,qual) ->
                             resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____732 FStar_List.rev in
             let rec aux body3 uu___200_751 =
               match uu___200_751 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____764 =
          let uu____767 =
            let uu____768 = FStar_Syntax_Syntax.mk_binder x in [uu____768] in
          FStar_Syntax_Subst.open_term uu____767 phi in
        (match uu____764 with
         | (x1,phi1) ->
             let uu____771 = FStar_List.hd x1 in
             (match uu____771 with
              | (b,uu____777) ->
                  let b1 = resugar_bv_as_binder b t.FStar_Syntax_Syntax.pos in
                  let uu____779 =
                    let uu____780 =
                      let uu____783 = resugar_term phi1 in (b1, uu____783) in
                    FStar_Parser_AST.Refine uu____780 in
                  mk1 uu____779))
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___201_813 =
          match uu___201_813 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____860 -> failwith "last of an empty list" in
        let rec last_two uu___202_884 =
          match uu___202_884 with
          | []|_::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____947::t1 -> last_two t1 in
        let rec last_three uu___203_975 =
          match uu___203_975 with
          | []|_::[]|_::_::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1065::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1101  ->
                    match uu____1101 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1115 = FStar_Options.print_implicits () in
          if uu____1115 then args else filter_imp args in
        let uu____1124 = resugar_term_as_op e in
        (match uu____1124 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1130) ->
             (match args1 with
              | (fst1,uu____1134)::(snd1,uu____1136)::rest ->
                  let e1 =
                    let uu____1160 =
                      let uu____1161 =
                        let uu____1165 =
                          let uu____1167 = resugar_term fst1 in
                          let uu____1168 =
                            let uu____1170 = resugar_term snd1 in
                            [uu____1170] in
                          uu____1167 :: uu____1168 in
                        ((FStar_Ident.id_of_text "*"), uu____1165) in
                      FStar_Parser_AST.Op uu____1161 in
                    mk1 uu____1160 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1175  ->
                         match uu____1175 with
                         | (x,uu____1179) ->
                             let uu____1180 =
                               let uu____1181 =
                                 let uu____1185 =
                                   let uu____1187 =
                                     let uu____1189 = resugar_term x in
                                     [uu____1189] in
                                   e1 :: uu____1187 in
                                 ((FStar_Ident.id_of_text "*"), uu____1185) in
                               FStar_Parser_AST.Op uu____1181 in
                             mk1 uu____1180) e1 rest
              | uu____1191 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1197) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1219)::[] -> b
               | uu____1232 -> failwith "wrong arguments to dtuple" in
             let uu____1240 =
               let uu____1241 = FStar_Syntax_Subst.compress body in
               uu____1241.FStar_Syntax_Syntax.n in
             (match uu____1240 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1246) ->
                  let uu____1269 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1269 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1275 = FStar_Options.print_implicits () in
                         if uu____1275 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun uu____1282  ->
                                 match uu____1282 with
                                 | (b,qual) ->
                                     resugar_bv_as_binder b
                                       t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1289 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1300  ->
                            match uu____1300 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1308) -> resugar_as_app e args1
         | Some (ref_read,uu____1312) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1315 = FStar_List.hd args1 in
             (match uu____1315 with
              | (t1,uu____1325) ->
                  let uu____1330 =
                    let uu____1331 = FStar_Syntax_Subst.compress t1 in
                    uu____1331.FStar_Syntax_Syntax.n in
                  (match uu____1330 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1344 =
                         let uu____1345 =
                           let uu____1348 = resugar_term t1 in
                           (uu____1348, f) in
                         FStar_Parser_AST.Project uu____1345 in
                       mk1 uu____1344
                   | uu____1349 -> resugar_term t1))
         | Some ("try_with",uu____1350) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1366 =
               match new_args with
               | (a1,uu____1380)::(a2,uu____1382)::[] -> (a1, a2)
               | uu____1407 -> failwith "wrong arguments to try_with" in
             (match uu____1366 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1433 =
                      let uu____1434 = FStar_Syntax_Subst.compress term in
                      uu____1434.FStar_Syntax_Syntax.n in
                    match uu____1433 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1439) ->
                        let uu____1462 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1462 with | (x1,e2) -> e2)
                    | uu____1467 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1469 = decomp body in resugar_term uu____1469 in
                  let handler1 =
                    let uu____1471 = decomp handler in
                    resugar_term uu____1471 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1477,uu____1478,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1495,uu____1496,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1509 =
                          let uu____1510 =
                            let uu____1515 = resugar_body t11 in
                            (uu____1515, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1510 in
                        mk1 uu____1509
                    | uu____1517 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1550 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1566) -> resugar_as_app e args1
         | Some (op,uu____1570) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body)|FStar_Parser_AST.QForall
                 (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1617 -> (xs, pat, t1) in
             let resugar body =
               let uu____1625 =
                 let uu____1626 = FStar_Syntax_Subst.compress body in
                 uu____1626.FStar_Syntax_Syntax.n in
               match uu____1625 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1631) ->
                   let uu____1654 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1654 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1660 = FStar_Options.print_implicits () in
                          if uu____1660 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun uu____1667  ->
                                  match uu____1667 with
                                  | (b,qual) ->
                                      resugar_bv_as_binder b
                                        t.FStar_Syntax_Syntax.pos)) in
                        let uu____1672 =
                          let uu____1677 =
                            let uu____1678 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1678.FStar_Syntax_Syntax.n in
                          match uu____1677 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let resugar_pats pats =
                                FStar_List.map
                                  (fun es  ->
                                     FStar_All.pipe_right es
                                       (FStar_List.map
                                          (fun uu____1720  ->
                                             match uu____1720 with
                                             | (e2,uu____1724) ->
                                                 resugar_term e2))) pats in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    resugar_pats pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1739) ->
                                    let uu____1740 =
                                      let uu____1742 =
                                        let uu____1743 = name s r in
                                        mk1 uu____1743 in
                                      [uu____1742] in
                                    [uu____1740]
                                | uu____1746 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1751 ->
                              let uu____1752 = resugar_term body2 in
                              ([], uu____1752) in
                        (match uu____1672 with
                         | (pats,body3) ->
                             let uu____1762 = uncurry xs3 pats body3 in
                             (match uu____1762 with
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
               | uu____1789 ->
                   if op = "forall"
                   then
                     let uu____1790 =
                       let uu____1791 =
                         let uu____1798 = resugar_term body in
                         ([], [[]], uu____1798) in
                       FStar_Parser_AST.QForall uu____1791 in
                     mk1 uu____1790
                   else
                     (let uu____1805 =
                        let uu____1806 =
                          let uu____1813 = resugar_term body in
                          ([], [[]], uu____1813) in
                        FStar_Parser_AST.QExists uu____1806 in
                      mk1 uu____1805) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1833)::[] -> resugar b
                | uu____1846 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1853) ->
             let uu____1856 = FStar_List.hd args1 in
             (match uu____1856 with | (e1,uu____1866) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1893  ->
                       match uu____1893 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1898 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1898 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1906 =
                         let uu____1907 =
                           let uu____1911 =
                             let uu____1913 = last1 args1 in
                             resugar uu____1913 in
                           (op1, uu____1911) in
                         FStar_Parser_AST.Op uu____1907 in
                       mk1 uu____1906
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1925 =
                         let uu____1926 =
                           let uu____1930 =
                             let uu____1932 = last_two args1 in
                             resugar uu____1932 in
                           (op1, uu____1930) in
                         FStar_Parser_AST.Op uu____1926 in
                       mk1 uu____1925
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1944 =
                         let uu____1945 =
                           let uu____1949 =
                             let uu____1951 = last_three args1 in
                             resugar uu____1951 in
                           (op1, uu____1949) in
                         FStar_Parser_AST.Op uu____1945 in
                       mk1 uu____1944
                   | uu____1956 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1964 =
                    let uu____1965 =
                      let uu____1969 =
                        let uu____1971 = last_two args1 in resugar uu____1971 in
                      (op1, uu____1969) in
                    FStar_Parser_AST.Op uu____1965 in
                  mk1 uu____1964
              | uu____1976 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1979,t1)::[]) when
        let uu____2030 = is_disj_pat pat in Prims.op_Negation uu____2030 ->
        let bnds =
          let uu____2035 =
            let uu____2038 = resugar_match_pat pat in
            let uu____2039 = resugar_term e in (uu____2038, uu____2039) in
          [uu____2035] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2050,t1)::(pat2,uu____2053,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2128 =
          let uu____2129 =
            let uu____2133 = resugar_term e in
            let uu____2134 = resugar_term t1 in
            let uu____2135 = resugar_term t2 in
            (uu____2133, uu____2134, uu____2135) in
          FStar_Parser_AST.If uu____2129 in
        mk1 uu____2128
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2175 =
          match uu____2175 with
          | (pat,wopt,b) ->
              let pat1 = resugar_match_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2194 = resugar_term e1 in Some uu____2194 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2197 =
          let uu____2198 =
            let uu____2206 = resugar_term e in
            let uu____2207 = FStar_List.map resugar_branch branches in
            (uu____2206, uu____2207) in
          FStar_Parser_AST.Match uu____2198 in
        mk1 uu____2197
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2229) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2282 =
          let uu____2283 =
            let uu____2288 = resugar_term e in (uu____2288, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2283 in
        mk1 uu____2282
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2306 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2306 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2322 =
                 let uu____2325 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2325 in
               match uu____2322 with
               | (univs1,td) ->
                   let uu____2332 =
                     let uu____2339 =
                       let uu____2340 = FStar_Syntax_Subst.compress td in
                       uu____2340.FStar_Syntax_Syntax.n in
                     match uu____2339 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2349,(t1,uu____2351)::(d,uu____2353)::[]) ->
                         (t1, d)
                     | uu____2387 -> failwith "wrong let binding format" in
                   (match uu____2332 with
                    | (typ,def) ->
                        let uu____2408 =
                          let uu____2412 =
                            let uu____2413 = FStar_Syntax_Subst.compress def in
                            uu____2413.FStar_Syntax_Syntax.n in
                          match uu____2412 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2421) ->
                              let uu____2444 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2444 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2453 =
                                       FStar_Options.print_implicits () in
                                     if uu____2453 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2455 -> ([], def, false) in
                        (match uu____2408 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2476 =
                                 FStar_Options.print_universes () in
                               if uu____2476
                               then
                                 let uu____2477 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2477
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2482 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2493 =
                                     let uu____2494 =
                                       let uu____2495 =
                                         let uu____2499 =
                                           bv_as_unique_ident bv in
                                         (uu____2499, None) in
                                       FStar_Parser_AST.PatVar uu____2495 in
                                     mk_pat uu____2494 in
                                   (uu____2493, term) in
                             (match uu____2482 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2516  ->
                                              match uu____2516 with
                                              | (bv,uu____2520) ->
                                                  let uu____2521 =
                                                    let uu____2522 =
                                                      let uu____2526 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2526, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2522 in
                                                  mk_pat uu____2521)) in
                                    let uu____2528 =
                                      let uu____2531 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2531) in
                                    let uu____2533 =
                                      universe_to_string univs1 in
                                    (uu____2528, uu____2533)
                                  else
                                    (let uu____2537 =
                                       let uu____2540 = resugar_term term1 in
                                       (pat, uu____2540) in
                                     let uu____2541 =
                                       universe_to_string univs1 in
                                     (uu____2537, uu____2541))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map Prims.fst r in
             let comments = FStar_List.map Prims.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2580) ->
        let s =
          let uu____2594 =
            let uu____2595 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2595 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2594 in
        let uu____2599 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2599
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___204_2609 =
          match uu___204_2609 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2610 =
                let uu____2611 = FStar_Syntax_Subst.compress e in
                uu____2611.FStar_Syntax_Syntax.n in
              (match uu____2610 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2637 =
                       let uu____2638 = FStar_Syntax_Subst.compress h in
                       uu____2638.FStar_Syntax_Syntax.n in
                     match uu____2637 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2645 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2645, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2653 = aux h1 in
                         (match uu____2653 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2665 -> failwith "wrong Data_app head format" in
                   let uu____2669 = aux head1 in
                   (match uu____2669 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2684 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2684, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2693  ->
                               match uu____2693 with
                               | (t1,uu____2699) ->
                                   let uu____2700 = resugar_term t1 in
                                   (uu____2700, FStar_Parser_AST.Nothing))
                            args in
                        if FStar_Syntax_Util.is_tuple_data_lid' head2
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2705 = FStar_Options.print_universes () in
                           if uu____2705
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2715,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2721,uu____2722) -> resugar_term e
                    | uu____2727 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2728 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2734,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2750 =
                      let uu____2751 =
                        let uu____2756 = resugar_seq t11 in
                        (uu____2756, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2751 in
                    mk1 uu____2750
                | uu____2758 -> t1 in
              resugar_seq term
          | FStar_Syntax_Syntax.Primop 
            |FStar_Syntax_Syntax.Masked_effect 
             |FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term e
          | FStar_Syntax_Syntax.Mutable_alloc  ->
              let term = resugar_term e in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier ,l,t1)
                   ->
                   mk1
                     (FStar_Parser_AST.Let (FStar_Parser_AST.Mutable, l, t1))
               | uu____2771 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2773 =
                let uu____2774 = FStar_Syntax_Subst.compress e in
                uu____2774.FStar_Syntax_Syntax.n in
              (match uu____2773 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2778;
                      FStar_Syntax_Syntax.pos = uu____2779;
                      FStar_Syntax_Syntax.vars = uu____2780;_},(term,uu____2782)::[])
                   -> resugar_term term
               | uu____2804 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2826  ->
                       match uu____2826 with
                       | (x,uu____2830) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2832,p) ->
             let uu____2834 =
               let uu____2835 =
                 let uu____2839 = resugar_term e in (uu____2839, l, p) in
               FStar_Parser_AST.Labeled uu____2835 in
             mk1 uu____2834
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1)
           |FStar_Syntax_Syntax.Meta_monadic_lift (name1,_,t1) ->
             let uu____2853 =
               let uu____2854 =
                 let uu____2859 = resugar_term e in
                 let uu____2860 =
                   let uu____2861 =
                     let uu____2862 =
                       let uu____2868 =
                         let uu____2872 =
                           let uu____2875 = resugar_term t1 in
                           (uu____2875, FStar_Parser_AST.Nothing) in
                         [uu____2872] in
                       (name1, uu____2868) in
                     FStar_Parser_AST.Construct uu____2862 in
                   mk1 uu____2861 in
                 (uu____2859, uu____2860, None) in
               FStar_Parser_AST.Ascribed uu____2854 in
             mk1 uu____2853)
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
             let uu____2906 = FStar_Options.print_universes () in
             if uu____2906
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
             let uu____2942 = FStar_Options.print_universes () in
             if uu____2942
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
          let uu____2965 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2965, FStar_Parser_AST.Nothing) in
        let uu____2966 = FStar_Options.print_effect_args () in
        if uu____2966
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___205_3006 =
                match uu___205_3006 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3048 -> aux l tl1
                     | uu____3053 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3073  ->
                 match uu____3073 with
                 | (e,uu____3079) ->
                     let uu____3080 = resugar_term e in
                     (uu____3080, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___206_3094 =
            match uu___206_3094 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3114 = resugar_term e in
                       (uu____3114, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3117 -> aux l tl1) in
          let decrease = aux [] c1.FStar_Syntax_Syntax.flags in
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name),
                 (FStar_List.append (result :: decrease) args1)))
        else
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name), [result]))
and resugar_bv_as_binder:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Parser_AST.binder =
  fun x  ->
    fun r  ->
      let e = resugar_term x.FStar_Syntax_Syntax.sort in
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Wild  ->
          let uu____3142 =
            let uu____3143 = bv_as_unique_ident x in
            FStar_Parser_AST.Variable uu____3143 in
          FStar_Parser_AST.mk_binder uu____3142 r FStar_Parser_AST.Type_level
            None
      | uu____3144 ->
          let uu____3145 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____3145
          then
            FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
              FStar_Parser_AST.Type_level None
          else
            (let uu____3147 =
               let uu____3148 =
                 let uu____3151 = bv_as_unique_ident x in (uu____3151, e) in
               FStar_Parser_AST.Annotated uu____3148 in
             FStar_Parser_AST.mk_binder uu____3147 r
               FStar_Parser_AST.Type_level None)
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern Prims.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3159 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3159 in
      let uu____3160 =
        let uu____3161 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3161.FStar_Syntax_Syntax.n in
      match uu____3160 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3167 = mk1 FStar_Parser_AST.PatWild in Some uu____3167
          else
            (let uu____3169 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3169
               (fun aq  ->
                  let uu____3175 =
                    let uu____3176 =
                      let uu____3177 =
                        let uu____3181 = bv_as_unique_ident x in
                        (uu____3181, aq) in
                      FStar_Parser_AST.PatVar uu____3177 in
                    mk1 uu____3176 in
                  Some uu____3175))
      | uu____3183 ->
          let uu____3184 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3184
            (fun aq  ->
               let pat =
                 let uu____3191 =
                   let uu____3192 =
                     let uu____3196 = bv_as_unique_ident x in
                     (uu____3196, aq) in
                   FStar_Parser_AST.PatVar uu____3192 in
                 mk1 uu____3191 in
               let uu____3198 = FStar_Options.print_bound_var_types () in
               if uu____3198
               then
                 let uu____3200 =
                   let uu____3201 =
                     let uu____3202 =
                       let uu____3205 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3205) in
                     FStar_Parser_AST.PatAscribed uu____3202 in
                   mk1 uu____3201 in
                 Some uu____3200
               else Some pat)
and resugar_match_pat: FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
    let rec aux p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
      | FStar_Syntax_Syntax.Pat_disj args ->
          let args1 = FStar_List.map (fun p2  -> aux p2) args in
          mk1 (FStar_Parser_AST.PatOr args1)
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
              (fun uu____3258  -> match uu____3258 with | (p2,b) -> aux p2)
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
              (fun uu____3287  -> match uu____3287 with | (p2,b) -> aux p2)
              args in
          if
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3299;
             FStar_Syntax_Syntax.fv_delta = uu____3300;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3321 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3321 FStar_List.rev in
          let args1 =
            let uu____3330 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3340  ->
                      match uu____3340 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3330 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3382 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3382
            | (hd1::tl1,hd2::tl2) ->
                let uu____3396 = map21 tl1 tl2 in (hd1, hd2) :: uu____3396 in
          let args2 =
            let uu____3406 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3406 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3434  -> match uu____3434 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3445 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3445 with
           | Some (op,uu____3450) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3455 =
                 let uu____3456 =
                   let uu____3460 = bv_as_unique_ident v1 in
                   (uu____3460, None) in
                 FStar_Parser_AST.PatVar uu____3456 in
               mk1 uu____3455)
      | FStar_Syntax_Syntax.Pat_wild uu____3462 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3470 =
              let uu____3471 =
                let uu____3475 = bv_as_unique_ident bv in (uu____3475, None) in
              FStar_Parser_AST.PatVar uu____3471 in
            mk1 uu____3470 in
          let uu____3477 = FStar_Options.print_bound_var_types () in
          if uu____3477
          then
            let uu____3478 =
              let uu____3479 =
                let uu____3482 = resugar_term term in (pat, uu____3482) in
              FStar_Parser_AST.PatAscribed uu____3479 in
            mk1 uu____3478
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier Prims.option =
  fun uu___207_3487  ->
    match uu___207_3487 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3493 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3494 -> None
    | FStar_Syntax_Syntax.Projector uu____3495 -> None
    | FStar_Syntax_Syntax.RecordType uu____3498 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3503 -> None
    | FStar_Syntax_Syntax.Action uu____3508 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___208_3511  ->
    match uu___208_3511 with
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
          (tylid,uvs,bs,t,uu____3533,datacons) ->
          let uu____3539 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3550,uu____3551,uu____3552,inductive_lid,uu____3554,uu____3555)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3558 -> failwith "unexpected")) in
          (match uu____3539 with
           | (current_datacons,other_datacons) ->
               let tyc =
                 let uu____3569 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___209_3571  ->
                           match uu___209_3571 with
                           | FStar_Syntax_Syntax.RecordType uu____3572 ->
                               true
                           | uu____3577 -> false)) in
                 if uu____3569 then failwith "NIY" else failwith "NIY" in
               (other_datacons, tyc))
      | FStar_Syntax_Syntax.Sig_declare_typ (tylid,uvs,t) -> failwith "NIY"
      | uu____3585 ->
          failwith
            "Impossible : only Sig_inductive_typ and Sig_declare_typ can be resugared as types"
let decl'_to_decl:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun se  ->
    fun d'  ->
      let uu____3594 =
        FStar_List.choose resugar_qualifier se.FStar_Syntax_Syntax.sigquals in
      {
        FStar_Parser_AST.d = d';
        FStar_Parser_AST.drange = (se.FStar_Syntax_Syntax.sigrng);
        FStar_Parser_AST.doc = None;
        FStar_Parser_AST.quals = uu____3594;
        FStar_Parser_AST.attrs = []
      }
let resugar_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Parser_AST.decl Prims.option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3602) ->
        let uu____3607 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ _
                    |FStar_Syntax_Syntax.Sig_declare_typ _ -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____3620 -> false
                  | uu____3628 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____3607 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____3648 se1 =
               match uu____3648 with
               | (datacon_ses1,tycons) ->
                   let uu____3663 = resugar_typ datacon_ses1 se1 in
                   (match uu____3663 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____3672 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____3672 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____3691 =
                         let uu____3692 =
                           let uu____3693 =
                             let uu____3700 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____3700) in
                           FStar_Parser_AST.Tycon uu____3693 in
                         decl'_to_decl se uu____3692 in
                       Some uu____3691
                   | se1::[] ->
                       let uu____3715 =
                         let uu____3716 =
                           let uu____3717 = failwith "NIY" in
                           FStar_Parser_AST.Exception uu____3717 in
                         decl'_to_decl se1 uu____3716 in
                       Some uu____3715
                   | uu____3724 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____3728,attrs) -> failwith "NIY"
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____3737 =
          let uu____3738 =
            let uu____3739 =
              let uu____3742 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____3742) in
            FStar_Parser_AST.Assume uu____3739 in
          decl'_to_decl se uu____3738 in
        Some uu____3737
    | FStar_Syntax_Syntax.Sig_new_effect ed -> failwith "NIY"
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed -> failwith "NIY"
    | FStar_Syntax_Syntax.Sig_sub_effect se1 -> failwith "NIY"
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        failwith "NIY"
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____3758 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____3758
    | FStar_Syntax_Syntax.Sig_inductive_typ _
      |FStar_Syntax_Syntax.Sig_declare_typ _
       |FStar_Syntax_Syntax.Sig_datacon _|FStar_Syntax_Syntax.Sig_main _ ->
        None