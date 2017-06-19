open Prims
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____6 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____6
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___195_40  ->
          match uu___195_40 with
          | (uu____44,Some (FStar_Syntax_Syntax.Implicit uu____45)) -> false
          | uu____47 -> true))
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
      | uu____84 -> (n1, u)
let rec resugar_universe:
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
      | FStar_Syntax_Syntax.U_succ uu____105 ->
          let uu____106 = universe_to_int (Prims.parse_int "0") u in
          (match uu____106 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____111 =
                      let uu____112 =
                        let uu____113 =
                          let uu____119 = FStar_Util.string_of_int n1 in
                          (uu____119, None) in
                        FStar_Const.Const_int uu____113 in
                      FStar_Parser_AST.Const uu____112 in
                    mk1 uu____111 r
                | uu____125 ->
                    let e1 =
                      let uu____127 =
                        let uu____128 =
                          let uu____129 =
                            let uu____135 = FStar_Util.string_of_int n1 in
                            (uu____135, None) in
                          FStar_Const.Const_int uu____129 in
                        FStar_Parser_AST.Const uu____128 in
                      mk1 uu____127 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____145 ->
               let t =
                 let uu____148 =
                   let uu____149 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____149 in
                 mk1 uu____148 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____152 =
                        let uu____153 =
                          let uu____157 = resugar_universe x r in
                          (acc, uu____157, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____153 in
                      mk1 uu____152 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____159 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____164 =
              let uu____167 =
                let uu____168 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____168 in
              (uu____167, r) in
            FStar_Ident.mk_ident uu____164 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op: Prims.string -> (Prims.string* Prims.int) option =
  fun s  ->
    let name_of_op uu___196_182 =
      match uu___196_182 with
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
      | uu____220 -> None in
    match s with
    | "op_String_Assignment" -> Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" -> Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" -> Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" -> Some (".()", (Prims.parse_int "0"))
    | uu____234 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____240 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____240 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____249 ->
               let op =
                 let uu____252 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some (op,uu____269) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____252 in
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
      let uu____368 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (fst d))) in
      match uu____368 with
      | Some op -> Some ((snd op), (Prims.parse_int "0"))
      | uu____393 ->
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
                (let uu____442 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____442
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
    let uu____455 =
      let uu____456 = FStar_Syntax_Subst.compress t in
      uu____456.FStar_Syntax_Syntax.n in
    match uu____455 with
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
        let uu____490 = string_to_op s in
        (match uu____490 with | Some t1 -> Some t1 | uu____504 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____514 -> None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____521 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____526 -> true
    | uu____527 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____555 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____555 in
    let var a r =
      let uu____563 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____563 in
    let uu____564 =
      let uu____565 = FStar_Syntax_Subst.compress t in
      uu____565.FStar_Syntax_Syntax.n in
    match uu____564 with
    | FStar_Syntax_Syntax.Tm_delayed uu____568 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____591 = let uu____593 = bv_as_unique_ident x in [uu____593] in
          FStar_Ident.lid_of_ids uu____591 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____596 = let uu____598 = bv_as_unique_ident x in [uu____598] in
          FStar_Ident.lid_of_ids uu____596 in
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
          let uu____630 =
            let uu____631 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____631 in
          mk1 uu____630
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
             | uu____644 -> failwith "wrong projector format")
          else
            (let uu____647 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____648 =
                    let uu____649 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____649 in
                  let uu____650 = FStar_String.get s (Prims.parse_int "0") in
                  uu____648 <> uu____650) in
             if uu____647
             then
               let uu____651 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____651
             else
               (let uu____653 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____653))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____660 = FStar_Options.print_universes () in
        if uu____660
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____664 =
                   let uu____665 =
                     let uu____669 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____669, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____665 in
                 mk1 uu____664) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____672 = FStar_Syntax_Syntax.is_teff t in
        if uu____672
        then
          let uu____673 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____673
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____676 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____676
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____677 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____677
         | uu____678 ->
             let uu____679 = FStar_Options.print_universes () in
             if uu____679
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____690 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____690))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____693) ->
        let uu____716 = FStar_Syntax_Subst.open_term xs body in
        (match uu____716 with
         | (xs1,body1) ->
             let xs2 =
               let uu____722 = FStar_Options.print_implicits () in
               if uu____722 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____729  ->
                       match uu____729 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____749 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____749 with
         | (xs1,body1) ->
             let xs2 =
               let uu____755 = FStar_Options.print_implicits () in
               if uu____755 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____760 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____760 FStar_List.rev in
             let rec aux body3 uu___197_773 =
               match uu___197_773 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____786 =
          let uu____789 =
            let uu____790 = FStar_Syntax_Syntax.mk_binder x in [uu____790] in
          FStar_Syntax_Subst.open_term uu____789 phi in
        (match uu____786 with
         | (x1,phi1) ->
             let b =
               let uu____794 = FStar_List.hd x1 in
               resugar_binder uu____794 t.FStar_Syntax_Syntax.pos in
             let uu____797 =
               let uu____798 =
                 let uu____801 = resugar_term phi1 in (b, uu____801) in
               FStar_Parser_AST.Refine uu____798 in
             mk1 uu____797)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___198_831 =
          match uu___198_831 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____878 -> failwith "last of an empty list" in
        let rec last_two uu___199_902 =
          match uu___199_902 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____922::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____974::t1 -> last_two t1 in
        let rec last_three uu___200_1002 =
          match uu___200_1002 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1022::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1040::uu____1041::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1114::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1150  ->
                    match uu____1150 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1164 = FStar_Options.print_implicits () in
          if uu____1164 then args else filter_imp args in
        let uu____1173 = resugar_term_as_op e in
        (match uu____1173 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1179) ->
             (match args1 with
              | (fst1,uu____1183)::(snd1,uu____1185)::rest ->
                  let e1 =
                    let uu____1209 =
                      let uu____1210 =
                        let uu____1214 =
                          let uu____1216 = resugar_term fst1 in
                          let uu____1217 =
                            let uu____1219 = resugar_term snd1 in
                            [uu____1219] in
                          uu____1216 :: uu____1217 in
                        ((FStar_Ident.id_of_text "*"), uu____1214) in
                      FStar_Parser_AST.Op uu____1210 in
                    mk1 uu____1209 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1224  ->
                         match uu____1224 with
                         | (x,uu____1228) ->
                             let uu____1229 =
                               let uu____1230 =
                                 let uu____1234 =
                                   let uu____1236 =
                                     let uu____1238 = resugar_term x in
                                     [uu____1238] in
                                   e1 :: uu____1236 in
                                 ((FStar_Ident.id_of_text "*"), uu____1234) in
                               FStar_Parser_AST.Op uu____1230 in
                             mk1 uu____1229) e1 rest
              | uu____1240 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1246) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1271)::[] -> b
               | uu____1284 -> failwith "wrong arguments to dtuple" in
             let uu____1292 =
               let uu____1293 = FStar_Syntax_Subst.compress body in
               uu____1293.FStar_Syntax_Syntax.n in
             (match uu____1292 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1298) ->
                  let uu____1321 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1321 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1327 = FStar_Options.print_implicits () in
                         if uu____1327 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1335 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1346  ->
                            match uu____1346 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1354) -> resugar_as_app e args1
         | Some (ref_read,uu____1358) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1361 = FStar_List.hd args1 in
             (match uu____1361 with
              | (t1,uu____1371) ->
                  let uu____1376 =
                    let uu____1377 = FStar_Syntax_Subst.compress t1 in
                    uu____1377.FStar_Syntax_Syntax.n in
                  (match uu____1376 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1390 =
                         let uu____1391 =
                           let uu____1394 = resugar_term t1 in
                           (uu____1394, f) in
                         FStar_Parser_AST.Project uu____1391 in
                       mk1 uu____1390
                   | uu____1395 -> resugar_term t1))
         | Some ("try_with",uu____1396) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1415 =
               match new_args with
               | (a1,uu____1429)::(a2,uu____1431)::[] -> (a1, a2)
               | uu____1456 -> failwith "wrong arguments to try_with" in
             (match uu____1415 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1482 =
                      let uu____1483 = FStar_Syntax_Subst.compress term in
                      uu____1483.FStar_Syntax_Syntax.n in
                    match uu____1482 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1488) ->
                        let uu____1511 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1511 with | (x1,e2) -> e2)
                    | uu____1516 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1518 = decomp body in resugar_term uu____1518 in
                  let handler1 =
                    let uu____1520 = decomp handler in
                    resugar_term uu____1520 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1526,uu____1527,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1544,uu____1545,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1558 =
                          let uu____1559 =
                            let uu____1564 = resugar_body t11 in
                            (uu____1564, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1559 in
                        mk1 uu____1558
                    | uu____1566 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1599 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1615) -> resugar_as_app e args1
         | Some (op,uu____1619) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1670 -> (xs, pat, t1) in
             let resugar body =
               let uu____1678 =
                 let uu____1679 = FStar_Syntax_Subst.compress body in
                 uu____1679.FStar_Syntax_Syntax.n in
               match uu____1678 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1684) ->
                   let uu____1707 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1707 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1713 = FStar_Options.print_implicits () in
                          if uu____1713 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1719 =
                          let uu____1724 =
                            let uu____1725 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1725.FStar_Syntax_Syntax.n in
                          match uu____1724 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1765  ->
                                                 match uu____1765 with
                                                 | (e2,uu____1769) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1772) ->
                                    let uu____1773 =
                                      let uu____1775 =
                                        let uu____1776 = name s r in
                                        mk1 uu____1776 in
                                      [uu____1775] in
                                    [uu____1773]
                                | uu____1779 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1784 ->
                              let uu____1785 = resugar_term body2 in
                              ([], uu____1785) in
                        (match uu____1719 with
                         | (pats,body3) ->
                             let uu____1795 = uncurry xs3 pats body3 in
                             (match uu____1795 with
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
               | uu____1822 ->
                   if op = "forall"
                   then
                     let uu____1823 =
                       let uu____1824 =
                         let uu____1831 = resugar_term body in
                         ([], [[]], uu____1831) in
                       FStar_Parser_AST.QForall uu____1824 in
                     mk1 uu____1823
                   else
                     (let uu____1838 =
                        let uu____1839 =
                          let uu____1846 = resugar_term body in
                          ([], [[]], uu____1846) in
                        FStar_Parser_AST.QExists uu____1839 in
                      mk1 uu____1838) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1869)::[] -> resugar b
                | uu____1882 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1889) ->
             let uu____1892 = FStar_List.hd args1 in
             (match uu____1892 with | (e1,uu____1902) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1929  ->
                       match uu____1929 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____1934 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1934 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1945 =
                         let uu____1946 =
                           let uu____1950 =
                             let uu____1952 = last1 args1 in
                             resugar uu____1952 in
                           (op1, uu____1950) in
                         FStar_Parser_AST.Op uu____1946 in
                       mk1 uu____1945
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1967 =
                         let uu____1968 =
                           let uu____1972 =
                             let uu____1974 = last_two args1 in
                             resugar uu____1974 in
                           (op1, uu____1972) in
                         FStar_Parser_AST.Op uu____1968 in
                       mk1 uu____1967
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1989 =
                         let uu____1990 =
                           let uu____1994 =
                             let uu____1996 = last_three args1 in
                             resugar uu____1996 in
                           (op1, uu____1994) in
                         FStar_Parser_AST.Op uu____1990 in
                       mk1 uu____1989
                   | uu____2001 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____2012 =
                    let uu____2013 =
                      let uu____2017 =
                        let uu____2019 = last_two args1 in resugar uu____2019 in
                      (op1, uu____2017) in
                    FStar_Parser_AST.Op uu____2013 in
                  mk1 uu____2012
              | uu____2024 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____2027,t1)::[]) ->
        let bnds =
          let uu____2082 =
            let uu____2085 = resugar_pat pat in
            let uu____2086 = resugar_term e in (uu____2085, uu____2086) in
          [uu____2082] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2097,t1)::(pat2,uu____2100,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2175 =
          let uu____2176 =
            let uu____2180 = resugar_term e in
            let uu____2181 = resugar_term t1 in
            let uu____2182 = resugar_term t2 in
            (uu____2180, uu____2181, uu____2182) in
          FStar_Parser_AST.If uu____2176 in
        mk1 uu____2175
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2222 =
          match uu____2222 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2241 = resugar_term e1 in Some uu____2241 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2244 =
          let uu____2245 =
            let uu____2253 = resugar_term e in
            let uu____2254 = FStar_List.map resugar_branch branches in
            (uu____2253, uu____2254) in
          FStar_Parser_AST.Match uu____2245 in
        mk1 uu____2244
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2276) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2329 =
          let uu____2330 =
            let uu____2335 = resugar_term e in (uu____2335, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2330 in
        mk1 uu____2329
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2353 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2353 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2369 =
                 let uu____2372 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2372 in
               match uu____2369 with
               | (univs1,td) ->
                   let uu____2379 =
                     let uu____2386 =
                       let uu____2387 = FStar_Syntax_Subst.compress td in
                       uu____2387.FStar_Syntax_Syntax.n in
                     match uu____2386 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2396,(t1,uu____2398)::(d,uu____2400)::[]) ->
                         (t1, d)
                     | uu____2434 -> failwith "wrong let binding format" in
                   (match uu____2379 with
                    | (typ,def) ->
                        let uu____2455 =
                          let uu____2459 =
                            let uu____2460 = FStar_Syntax_Subst.compress def in
                            uu____2460.FStar_Syntax_Syntax.n in
                          match uu____2459 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2468) ->
                              let uu____2491 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2491 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2500 =
                                       FStar_Options.print_implicits () in
                                     if uu____2500 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2502 -> ([], def, false) in
                        (match uu____2455 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2523 =
                                 FStar_Options.print_universes () in
                               if uu____2523
                               then
                                 let uu____2524 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2524
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2529 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2540 =
                                     let uu____2541 =
                                       let uu____2542 =
                                         let uu____2546 =
                                           bv_as_unique_ident bv in
                                         (uu____2546, None) in
                                       FStar_Parser_AST.PatVar uu____2542 in
                                     mk_pat uu____2541 in
                                   (uu____2540, term) in
                             (match uu____2529 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2563  ->
                                              match uu____2563 with
                                              | (bv,uu____2567) ->
                                                  let uu____2568 =
                                                    let uu____2569 =
                                                      let uu____2573 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2573, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2569 in
                                                  mk_pat uu____2568)) in
                                    let uu____2575 =
                                      let uu____2578 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2578) in
                                    let uu____2580 =
                                      universe_to_string univs1 in
                                    (uu____2575, uu____2580)
                                  else
                                    (let uu____2584 =
                                       let uu____2587 = resugar_term term1 in
                                       (pat, uu____2587) in
                                     let uu____2588 =
                                       universe_to_string univs1 in
                                     (uu____2584, uu____2588))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2627) ->
        let s =
          let uu____2641 =
            let uu____2642 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2642 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2641 in
        let uu____2643 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2643
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___201_2653 =
          match uu___201_2653 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2654 =
                let uu____2655 = FStar_Syntax_Subst.compress e in
                uu____2655.FStar_Syntax_Syntax.n in
              (match uu____2654 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2681 =
                       let uu____2682 = FStar_Syntax_Subst.compress h in
                       uu____2682.FStar_Syntax_Syntax.n in
                     match uu____2681 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2689 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2689, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2697 = aux h1 in
                         (match uu____2697 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2709 -> failwith "wrong Data_app head format" in
                   let uu____2713 = aux head1 in
                   (match uu____2713 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2728 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2728, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2737  ->
                               match uu____2737 with
                               | (t1,uu____2743) ->
                                   let uu____2744 = resugar_term t1 in
                                   (uu____2744, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2745 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2745
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2750 = FStar_Options.print_universes () in
                           if uu____2750
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2760,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2766,uu____2767) -> resugar_term e
                    | uu____2772 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2773 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2779,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2795 =
                      let uu____2796 =
                        let uu____2801 = resugar_seq t11 in
                        (uu____2801, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2796 in
                    mk1 uu____2795
                | uu____2803 -> t1 in
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
               | uu____2816 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2818 =
                let uu____2819 = FStar_Syntax_Subst.compress e in
                uu____2819.FStar_Syntax_Syntax.n in
              (match uu____2818 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2823;
                      FStar_Syntax_Syntax.pos = uu____2824;
                      FStar_Syntax_Syntax.vars = uu____2825;_},(term,uu____2827)::[])
                   -> resugar_term term
               | uu____2849 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2871  ->
                       match uu____2871 with
                       | (x,uu____2875) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2877,p) ->
             let uu____2879 =
               let uu____2880 =
                 let uu____2884 = resugar_term e in (uu____2884, l, p) in
               FStar_Parser_AST.Labeled uu____2880 in
             mk1 uu____2879
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____2886,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2895 =
               let uu____2896 =
                 let uu____2901 = resugar_term e in
                 let uu____2902 =
                   let uu____2903 =
                     let uu____2904 =
                       let uu____2910 =
                         let uu____2914 =
                           let uu____2917 = resugar_term t1 in
                           (uu____2917, FStar_Parser_AST.Nothing) in
                         [uu____2914] in
                       (name1, uu____2910) in
                     FStar_Parser_AST.Construct uu____2904 in
                   mk1 uu____2903 in
                 (uu____2901, uu____2902, None) in
               FStar_Parser_AST.Ascribed uu____2896 in
             mk1 uu____2895
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2927,t1) ->
             let uu____2933 =
               let uu____2934 =
                 let uu____2939 = resugar_term e in
                 let uu____2940 =
                   let uu____2941 =
                     let uu____2942 =
                       let uu____2948 =
                         let uu____2952 =
                           let uu____2955 = resugar_term t1 in
                           (uu____2955, FStar_Parser_AST.Nothing) in
                         [uu____2952] in
                       (name1, uu____2948) in
                     FStar_Parser_AST.Construct uu____2942 in
                   mk1 uu____2941 in
                 (uu____2939, uu____2940, None) in
               FStar_Parser_AST.Ascribed uu____2934 in
             mk1 uu____2933)
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
             let uu____2986 = FStar_Options.print_universes () in
             if uu____2986
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
             let uu____3022 = FStar_Options.print_universes () in
             if uu____3022
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
          let uu____3045 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____3045, FStar_Parser_AST.Nothing) in
        let uu____3046 = FStar_Options.print_effect_args () in
        if uu____3046
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___202_3086 =
                match uu___202_3086 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3128 -> aux l tl1
                     | uu____3133 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3153  ->
                 match uu____3153 with
                 | (e,uu____3159) ->
                     let uu____3160 = resugar_term e in
                     (uu____3160, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___203_3174 =
            match uu___203_3174 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3194 = resugar_term e in
                       (uu____3194, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3197 -> aux l tl1) in
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
      let uu____3221 = b in
      match uu____3221 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3225 =
                 let uu____3226 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3226 in
               FStar_Parser_AST.mk_binder uu____3225 r
                 FStar_Parser_AST.Type_level None
           | uu____3227 ->
               let uu____3228 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3228
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3230 =
                    let uu____3231 =
                      let uu____3234 = bv_as_unique_ident x in
                      (uu____3234, e) in
                    FStar_Parser_AST.Annotated uu____3231 in
                  FStar_Parser_AST.mk_binder uu____3230 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3242 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3242 in
      let uu____3243 =
        let uu____3244 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3244.FStar_Syntax_Syntax.n in
      match uu____3243 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3250 = mk1 FStar_Parser_AST.PatWild in Some uu____3250
          else
            (let uu____3252 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3252
               (fun aq  ->
                  let uu____3258 =
                    let uu____3259 =
                      let uu____3260 =
                        let uu____3264 = bv_as_unique_ident x in
                        (uu____3264, aq) in
                      FStar_Parser_AST.PatVar uu____3260 in
                    mk1 uu____3259 in
                  Some uu____3258))
      | uu____3266 ->
          let uu____3267 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3267
            (fun aq  ->
               let pat =
                 let uu____3274 =
                   let uu____3275 =
                     let uu____3279 = bv_as_unique_ident x in
                     (uu____3279, aq) in
                   FStar_Parser_AST.PatVar uu____3275 in
                 mk1 uu____3274 in
               let uu____3281 = FStar_Options.print_bound_var_types () in
               if uu____3281
               then
                 let uu____3283 =
                   let uu____3284 =
                     let uu____3285 =
                       let uu____3288 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3288) in
                     FStar_Parser_AST.PatAscribed uu____3285 in
                   mk1 uu____3284 in
                 Some uu____3283
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
              (fun uu____3334  -> match uu____3334 with | (p2,b) -> aux p2)
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
              (fun uu____3363  -> match uu____3363 with | (p2,b) -> aux p2)
              args in
          let uu____3368 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3368
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3376;
             FStar_Syntax_Syntax.fv_delta = uu____3377;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3398 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3398 FStar_List.rev in
          let args1 =
            let uu____3407 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3417  ->
                      match uu____3417 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3407 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3459 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3459
            | (hd1::tl1,hd2::tl2) ->
                let uu____3473 = map21 tl1 tl2 in (hd1, hd2) :: uu____3473 in
          let args2 =
            let uu____3483 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3483 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3511  -> match uu____3511 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3522 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3522 with
           | Some (op,uu____3527) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3532 =
                 let uu____3533 =
                   let uu____3537 = bv_as_unique_ident v1 in
                   (uu____3537, None) in
                 FStar_Parser_AST.PatVar uu____3533 in
               mk1 uu____3532)
      | FStar_Syntax_Syntax.Pat_wild uu____3539 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3547 =
              let uu____3548 =
                let uu____3552 = bv_as_unique_ident bv in (uu____3552, None) in
              FStar_Parser_AST.PatVar uu____3548 in
            mk1 uu____3547 in
          let uu____3554 = FStar_Options.print_bound_var_types () in
          if uu____3554
          then
            let uu____3555 =
              let uu____3556 =
                let uu____3559 = resugar_term term in (pat, uu____3559) in
              FStar_Parser_AST.PatAscribed uu____3556 in
            mk1 uu____3555
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___204_3565  ->
    match uu___204_3565 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3571 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3572 -> None
    | FStar_Syntax_Syntax.Projector uu____3573 -> None
    | FStar_Syntax_Syntax.RecordType uu____3576 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3581 -> None
    | FStar_Syntax_Syntax.Action uu____3586 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___205_3590  ->
    match uu___205_3590 with
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
          (tylid,uvs,bs,t,uu____3614,datacons) ->
          let uu____3620 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3631,uu____3632,uu____3633,inductive_lid,uu____3635,uu____3636)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3639 -> failwith "unexpected")) in
          (match uu____3620 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3650 = FStar_Options.print_implicits () in
                 if uu____3650 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3657 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___206_3659  ->
                           match uu___206_3659 with
                           | FStar_Syntax_Syntax.RecordType uu____3660 ->
                               true
                           | uu____3665 -> false)) in
                 if uu____3657
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3693,univs1,term,uu____3696,num,uu____3698)
                         ->
                         let uu____3701 =
                           let uu____3702 = FStar_Syntax_Subst.compress term in
                           uu____3702.FStar_Syntax_Syntax.n in
                         (match uu____3701 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3711) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3742  ->
                                        match uu____3742 with
                                        | (b,qual) ->
                                            let uu____3751 =
                                              let uu____3752 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3752 in
                                            let uu____3753 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3751, uu____3753, None))) in
                              FStar_List.append mfields fields
                          | uu____3759 -> failwith "unexpected")
                     | uu____3765 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3832,num,uu____3834) ->
                          let c =
                            let uu____3844 =
                              let uu____3846 = resugar_term term in
                              Some uu____3846 in
                            ((l.FStar_Ident.ident), uu____3844, None, false) in
                          c :: constructors
                      | uu____3855 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3894 ->
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
        let uu____3911 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3911;
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
      let uu____3928 = ts in
      match uu____3928 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3934 =
            let uu____3935 =
              let uu____3942 =
                let uu____3947 =
                  let uu____3951 =
                    let uu____3952 =
                      let uu____3959 = resugar_term typ in
                      (name1, [], None, uu____3959) in
                    FStar_Parser_AST.TyconAbbrev uu____3952 in
                  (uu____3951, None) in
                [uu____3947] in
              (false, uu____3942) in
            FStar_Parser_AST.Tycon uu____3935 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3934
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
            let uu____4003 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____4003 with
            | (bs,action_defn) ->
                let uu____4008 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____4008 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____4014 = FStar_Options.print_implicits () in
                       if uu____4014
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____4018 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____4018 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____4027 =
                           let uu____4033 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____4033,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____4027 in
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
          let uu____4072 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4072 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4078 = FStar_Options.print_implicits () in
                if uu____4078 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4082 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4082 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4124) ->
        let uu____4129 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4140 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4149 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4153 -> false
                  | uu____4161 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4129 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4181 se1 =
               match uu____4181 with
               | (datacon_ses1,tycons) ->
                   let uu____4196 = resugar_typ datacon_ses1 se1 in
                   (match uu____4196 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4205 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4205 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4224 =
                         let uu____4225 =
                           let uu____4226 =
                             let uu____4233 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4233) in
                           FStar_Parser_AST.Tycon uu____4226 in
                         decl'_to_decl se uu____4225 in
                       Some uu____4224
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4250,uu____4251,uu____4252,uu____4253,uu____4254)
                            ->
                            let uu____4257 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4257
                        | uu____4259 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4261 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4265,attrs) ->
        let uu____4271 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___207_4273  ->
                  match uu___207_4273 with
                  | FStar_Syntax_Syntax.Projector (uu____4274,uu____4275) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4276 -> true
                  | uu____4277 -> false)) in
        if uu____4271
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4302) ->
               let uu____4309 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4309
           | uu____4313 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4317 =
          let uu____4318 =
            let uu____4319 =
              let uu____4322 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4322) in
            FStar_Parser_AST.Assume uu____4319 in
          decl'_to_decl se uu____4318 in
        Some uu____4317
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4324 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4324
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4326 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4326
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4333,t) ->
              let uu____4340 = resugar_term t in Some uu____4340
          | uu____4341 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4346,t) ->
              let uu____4353 = resugar_term t in Some uu____4353
          | uu____4354 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4369 -> failwith "Should not happen hopefully" in
        let uu____4374 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4374
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4382 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4382 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4389 = FStar_Options.print_implicits () in
               if uu____4389 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4395 =
               let uu____4396 =
                 let uu____4397 =
                   let uu____4404 =
                     let uu____4409 =
                       let uu____4413 =
                         let uu____4414 =
                           let uu____4421 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4421) in
                         FStar_Parser_AST.TyconAbbrev uu____4414 in
                       (uu____4413, None) in
                     [uu____4409] in
                   (false, uu____4404) in
                 FStar_Parser_AST.Tycon uu____4397 in
               decl'_to_decl se uu____4396 in
             Some uu____4395)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4436 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4436
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4440 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___208_4442  ->
                  match uu___208_4442 with
                  | FStar_Syntax_Syntax.Projector (uu____4443,uu____4444) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4445 -> true
                  | uu____4446 -> false)) in
        if uu____4440
        then None
        else
          (let uu____4449 =
             let uu____4450 =
               let uu____4451 =
                 let uu____4454 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4454) in
               FStar_Parser_AST.Val uu____4451 in
             decl'_to_decl se uu____4450 in
           Some uu____4449)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4455 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4464 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4472 -> None