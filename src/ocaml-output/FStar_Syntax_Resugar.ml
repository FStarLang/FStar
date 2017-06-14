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
       (fun uu___184_37  ->
          match uu___184_37 with
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
    let name_of_op uu___185_175 =
      match uu___185_175 with
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
                (let uu____414 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____414
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
    let uu____423 =
      let uu____424 = FStar_Syntax_Subst.compress t in
      uu____424.FStar_Syntax_Syntax.n in
    match uu____423 with
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
        let uu____440 = string_to_op s in
        (match uu____440 with | Some t1 -> Some t1 | uu____454 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____464 -> None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____470 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____474 -> true
    | uu____475 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____503 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____503 in
    let var a r =
      let uu____511 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____511 in
    let uu____512 =
      let uu____513 = FStar_Syntax_Subst.compress t in
      uu____513.FStar_Syntax_Syntax.n in
    match uu____512 with
    | FStar_Syntax_Syntax.Tm_delayed uu____516 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____539 = let uu____541 = bv_as_unique_ident x in [uu____541] in
          FStar_Ident.lid_of_ids uu____539 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____544 = let uu____546 = bv_as_unique_ident x in [uu____546] in
          FStar_Ident.lid_of_ids uu____544 in
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
          let uu____562 =
            let uu____563 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____563 in
          mk1 uu____562
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
             | uu____574 -> failwith "wrong projector format")
          else
            (let uu____577 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____578 =
                    let uu____579 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____579 in
                  let uu____580 = FStar_String.get s (Prims.parse_int "0") in
                  uu____578 <> uu____580) in
             if uu____577
             then
               let uu____581 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____581
             else
               (let uu____583 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____583))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____590 = FStar_Options.print_universes () in
        if uu____590
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____594 =
                   let uu____595 =
                     let uu____599 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____599, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____595 in
                 mk1 uu____594) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____602 = FStar_Syntax_Syntax.is_teff t in
        if uu____602
        then
          let uu____603 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____603
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____606 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____606
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____607 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____607
         | uu____608 ->
             let uu____609 = FStar_Options.print_universes () in
             if uu____609
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____620 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____620))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____623) ->
        let uu____646 = FStar_Syntax_Subst.open_term xs body in
        (match uu____646 with
         | (xs1,body1) ->
             let xs2 =
               let uu____652 = FStar_Options.print_implicits () in
               if uu____652 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____659  ->
                       match uu____659 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____679 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____679 with
         | (xs1,body1) ->
             let xs2 =
               let uu____685 = FStar_Options.print_implicits () in
               if uu____685 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____690 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____690 FStar_List.rev in
             let rec aux body3 uu___186_703 =
               match uu___186_703 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____716 =
          let uu____719 =
            let uu____720 = FStar_Syntax_Syntax.mk_binder x in [uu____720] in
          FStar_Syntax_Subst.open_term uu____719 phi in
        (match uu____716 with
         | (x1,phi1) ->
             let b =
               let uu____724 = FStar_List.hd x1 in
               resugar_binder uu____724 t.FStar_Syntax_Syntax.pos in
             let uu____727 =
               let uu____728 =
                 let uu____731 = resugar_term phi1 in (b, uu____731) in
               FStar_Parser_AST.Refine uu____728 in
             mk1 uu____727)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___187_761 =
          match uu___187_761 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____808 -> failwith "last of an empty list" in
        let rec last_two uu___188_832 =
          match uu___188_832 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____852::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____904::t1 -> last_two t1 in
        let rec last_three uu___189_932 =
          match uu___189_932 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____952::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____970::uu____971::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1044::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1080  ->
                    match uu____1080 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1094 = FStar_Options.print_implicits () in
          if uu____1094 then args else filter_imp args in
        let uu____1103 = resugar_term_as_op e in
        (match uu____1103 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1109) ->
             (match args1 with
              | (fst1,uu____1113)::(snd1,uu____1115)::rest ->
                  let e1 =
                    let uu____1139 =
                      let uu____1140 =
                        let uu____1144 =
                          let uu____1146 = resugar_term fst1 in
                          let uu____1147 =
                            let uu____1149 = resugar_term snd1 in
                            [uu____1149] in
                          uu____1146 :: uu____1147 in
                        ((FStar_Ident.id_of_text "*"), uu____1144) in
                      FStar_Parser_AST.Op uu____1140 in
                    mk1 uu____1139 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1154  ->
                         match uu____1154 with
                         | (x,uu____1158) ->
                             let uu____1159 =
                               let uu____1160 =
                                 let uu____1164 =
                                   let uu____1166 =
                                     let uu____1168 = resugar_term x in
                                     [uu____1168] in
                                   e1 :: uu____1166 in
                                 ((FStar_Ident.id_of_text "*"), uu____1164) in
                               FStar_Parser_AST.Op uu____1160 in
                             mk1 uu____1159) e1 rest
              | uu____1170 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1176) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1198)::[] -> b
               | uu____1211 -> failwith "wrong arguments to dtuple" in
             let uu____1219 =
               let uu____1220 = FStar_Syntax_Subst.compress body in
               uu____1220.FStar_Syntax_Syntax.n in
             (match uu____1219 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1225) ->
                  let uu____1248 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1248 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1254 = FStar_Options.print_implicits () in
                         if uu____1254 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1262 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1273  ->
                            match uu____1273 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1281) -> resugar_as_app e args1
         | Some (ref_read,uu____1285) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1288 = FStar_List.hd args1 in
             (match uu____1288 with
              | (t1,uu____1298) ->
                  let uu____1303 =
                    let uu____1304 = FStar_Syntax_Subst.compress t1 in
                    uu____1304.FStar_Syntax_Syntax.n in
                  (match uu____1303 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1309 =
                         let uu____1310 =
                           let uu____1313 = resugar_term t1 in
                           (uu____1313, f) in
                         FStar_Parser_AST.Project uu____1310 in
                       mk1 uu____1309
                   | uu____1314 -> resugar_term t1))
         | Some ("try_with",uu____1315) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1331 =
               match new_args with
               | (a1,uu____1345)::(a2,uu____1347)::[] -> (a1, a2)
               | uu____1372 -> failwith "wrong arguments to try_with" in
             (match uu____1331 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1398 =
                      let uu____1399 = FStar_Syntax_Subst.compress term in
                      uu____1399.FStar_Syntax_Syntax.n in
                    match uu____1398 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1404) ->
                        let uu____1427 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1427 with | (x1,e2) -> e2)
                    | uu____1432 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1434 = decomp body in resugar_term uu____1434 in
                  let handler1 =
                    let uu____1436 = decomp handler in
                    resugar_term uu____1436 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1442,uu____1443,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1460,uu____1461,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1474 =
                          let uu____1475 =
                            let uu____1480 = resugar_body t11 in
                            (uu____1480, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1475 in
                        mk1 uu____1474
                    | uu____1482 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1515 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1531) -> resugar_as_app e args1
         | Some (op,uu____1535) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1586 -> (xs, pat, t1) in
             let resugar body =
               let uu____1594 =
                 let uu____1595 = FStar_Syntax_Subst.compress body in
                 uu____1595.FStar_Syntax_Syntax.n in
               match uu____1594 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1600) ->
                   let uu____1623 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1623 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1629 = FStar_Options.print_implicits () in
                          if uu____1629 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1635 =
                          let uu____1640 =
                            let uu____1641 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1641.FStar_Syntax_Syntax.n in
                          match uu____1640 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1681  ->
                                                 match uu____1681 with
                                                 | (e2,uu____1685) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1688) ->
                                    let uu____1689 =
                                      let uu____1691 =
                                        let uu____1692 = name s r in
                                        mk1 uu____1692 in
                                      [uu____1691] in
                                    [uu____1689]
                                | uu____1695 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1700 ->
                              let uu____1701 = resugar_term body2 in
                              ([], uu____1701) in
                        (match uu____1635 with
                         | (pats,body3) ->
                             let uu____1711 = uncurry xs3 pats body3 in
                             (match uu____1711 with
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
               | uu____1738 ->
                   if op = "forall"
                   then
                     let uu____1739 =
                       let uu____1740 =
                         let uu____1747 = resugar_term body in
                         ([], [[]], uu____1747) in
                       FStar_Parser_AST.QForall uu____1740 in
                     mk1 uu____1739
                   else
                     (let uu____1754 =
                        let uu____1755 =
                          let uu____1762 = resugar_term body in
                          ([], [[]], uu____1762) in
                        FStar_Parser_AST.QExists uu____1755 in
                      mk1 uu____1754) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1782)::[] -> resugar b
                | uu____1795 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1802) ->
             let uu____1805 = FStar_List.hd args1 in
             (match uu____1805 with | (e1,uu____1815) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1842  ->
                       match uu____1842 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1847 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1847 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1855 =
                         let uu____1856 =
                           let uu____1860 =
                             let uu____1862 = last1 args1 in
                             resugar uu____1862 in
                           (op1, uu____1860) in
                         FStar_Parser_AST.Op uu____1856 in
                       mk1 uu____1855
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1874 =
                         let uu____1875 =
                           let uu____1879 =
                             let uu____1881 = last_two args1 in
                             resugar uu____1881 in
                           (op1, uu____1879) in
                         FStar_Parser_AST.Op uu____1875 in
                       mk1 uu____1874
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1893 =
                         let uu____1894 =
                           let uu____1898 =
                             let uu____1900 = last_three args1 in
                             resugar uu____1900 in
                           (op1, uu____1898) in
                         FStar_Parser_AST.Op uu____1894 in
                       mk1 uu____1893
                   | uu____1905 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1913 =
                    let uu____1914 =
                      let uu____1918 =
                        let uu____1920 = last_two args1 in resugar uu____1920 in
                      (op1, uu____1918) in
                    FStar_Parser_AST.Op uu____1914 in
                  mk1 uu____1913
              | uu____1925 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1928,t1)::[]) ->
        let bnds =
          let uu____1978 =
            let uu____1981 = resugar_pat pat in
            let uu____1982 = resugar_term e in (uu____1981, uu____1982) in
          [uu____1978] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____1993,t1)::(pat2,uu____1996,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2063 =
          let uu____2064 =
            let uu____2068 = resugar_term e in
            let uu____2069 = resugar_term t1 in
            let uu____2070 = resugar_term t2 in
            (uu____2068, uu____2069, uu____2070) in
          FStar_Parser_AST.If uu____2064 in
        mk1 uu____2063
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2108 =
          match uu____2108 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2127 = resugar_term e1 in Some uu____2127 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2130 =
          let uu____2131 =
            let uu____2139 = resugar_term e in
            let uu____2140 = FStar_List.map resugar_branch branches in
            (uu____2139, uu____2140) in
          FStar_Parser_AST.Match uu____2131 in
        mk1 uu____2130
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2162) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2215 =
          let uu____2216 =
            let uu____2221 = resugar_term e in (uu____2221, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2216 in
        mk1 uu____2215
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2239 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2239 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2255 =
                 let uu____2258 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2258 in
               match uu____2255 with
               | (univs1,td) ->
                   let uu____2265 =
                     let uu____2272 =
                       let uu____2273 = FStar_Syntax_Subst.compress td in
                       uu____2273.FStar_Syntax_Syntax.n in
                     match uu____2272 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2282,(t1,uu____2284)::(d,uu____2286)::[]) ->
                         (t1, d)
                     | uu____2320 -> failwith "wrong let binding format" in
                   (match uu____2265 with
                    | (typ,def) ->
                        let uu____2341 =
                          let uu____2345 =
                            let uu____2346 = FStar_Syntax_Subst.compress def in
                            uu____2346.FStar_Syntax_Syntax.n in
                          match uu____2345 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2354) ->
                              let uu____2377 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2377 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2386 =
                                       FStar_Options.print_implicits () in
                                     if uu____2386 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2388 -> ([], def, false) in
                        (match uu____2341 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2409 =
                                 FStar_Options.print_universes () in
                               if uu____2409
                               then
                                 let uu____2410 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2410
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2415 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2422 =
                                     let uu____2423 =
                                       let uu____2424 =
                                         let uu____2428 =
                                           bv_as_unique_ident bv in
                                         (uu____2428, None) in
                                       FStar_Parser_AST.PatVar uu____2424 in
                                     mk_pat uu____2423 in
                                   (uu____2422, term) in
                             (match uu____2415 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2445  ->
                                              match uu____2445 with
                                              | (bv,uu____2449) ->
                                                  let uu____2450 =
                                                    let uu____2451 =
                                                      let uu____2455 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2455, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2451 in
                                                  mk_pat uu____2450)) in
                                    let uu____2457 =
                                      let uu____2460 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2460) in
                                    let uu____2462 =
                                      universe_to_string univs1 in
                                    (uu____2457, uu____2462)
                                  else
                                    (let uu____2466 =
                                       let uu____2469 = resugar_term term1 in
                                       (pat, uu____2469) in
                                     let uu____2470 =
                                       universe_to_string univs1 in
                                     (uu____2466, uu____2470))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2509) ->
        let s =
          let uu____2527 =
            let uu____2528 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2528 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2527 in
        let uu____2529 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2529
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___190_2539 =
          match uu___190_2539 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2540 =
                let uu____2541 = FStar_Syntax_Subst.compress e in
                uu____2541.FStar_Syntax_Syntax.n in
              (match uu____2540 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2567 =
                       let uu____2568 = FStar_Syntax_Subst.compress h in
                       uu____2568.FStar_Syntax_Syntax.n in
                     match uu____2567 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2575 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2575, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2583 = aux h1 in
                         (match uu____2583 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2595 -> failwith "wrong Data_app head format" in
                   let uu____2599 = aux head1 in
                   (match uu____2599 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2614 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2614, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2623  ->
                               match uu____2623 with
                               | (t1,uu____2629) ->
                                   let uu____2630 = resugar_term t1 in
                                   (uu____2630, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2631 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2631
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2636 = FStar_Options.print_universes () in
                           if uu____2636
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2646,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2652,uu____2653) -> resugar_term e
                    | uu____2658 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2659 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2665,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2681 =
                      let uu____2682 =
                        let uu____2687 = resugar_seq t11 in
                        (uu____2687, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2682 in
                    mk1 uu____2681
                | uu____2689 -> t1 in
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
               | uu____2702 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2704 =
                let uu____2705 = FStar_Syntax_Subst.compress e in
                uu____2705.FStar_Syntax_Syntax.n in
              (match uu____2704 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2709;
                      FStar_Syntax_Syntax.pos = uu____2710;
                      FStar_Syntax_Syntax.vars = uu____2711;_},(term,uu____2713)::[])
                   -> resugar_term term
               | uu____2735 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2757  ->
                       match uu____2757 with
                       | (x,uu____2761) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2763,p) ->
             let uu____2765 =
               let uu____2766 =
                 let uu____2770 = resugar_term e in (uu____2770, l, p) in
               FStar_Parser_AST.Labeled uu____2766 in
             mk1 uu____2765
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2779 =
               let uu____2780 =
                 let uu____2785 = resugar_term e in
                 let uu____2786 =
                   let uu____2787 =
                     let uu____2788 =
                       let uu____2794 =
                         let uu____2798 =
                           let uu____2801 = resugar_term t1 in
                           (uu____2801, FStar_Parser_AST.Nothing) in
                         [uu____2798] in
                       (name1, uu____2794) in
                     FStar_Parser_AST.Construct uu____2788 in
                   mk1 uu____2787 in
                 (uu____2785, uu____2786, None) in
               FStar_Parser_AST.Ascribed uu____2780 in
             mk1 uu____2779
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2811,t1) ->
             let uu____2817 =
               let uu____2818 =
                 let uu____2823 = resugar_term e in
                 let uu____2824 =
                   let uu____2825 =
                     let uu____2826 =
                       let uu____2832 =
                         let uu____2836 =
                           let uu____2839 = resugar_term t1 in
                           (uu____2839, FStar_Parser_AST.Nothing) in
                         [uu____2836] in
                       (name1, uu____2832) in
                     FStar_Parser_AST.Construct uu____2826 in
                   mk1 uu____2825 in
                 (uu____2823, uu____2824, None) in
               FStar_Parser_AST.Ascribed uu____2818 in
             mk1 uu____2817)
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
             let uu____2870 = FStar_Options.print_universes () in
             if uu____2870
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
             let uu____2906 = FStar_Options.print_universes () in
             if uu____2906
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
          let uu____2929 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2929, FStar_Parser_AST.Nothing) in
        let uu____2930 = FStar_Options.print_effect_args () in
        if uu____2930
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___191_2970 =
                match uu___191_2970 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3012 -> aux l tl1
                     | uu____3017 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3037  ->
                 match uu____3037 with
                 | (e,uu____3043) ->
                     let uu____3044 = resugar_term e in
                     (uu____3044, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___192_3058 =
            match uu___192_3058 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3078 = resugar_term e in
                       (uu____3078, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3081 -> aux l tl1) in
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
      let uu____3105 = b in
      match uu____3105 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3109 =
                 let uu____3110 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3110 in
               FStar_Parser_AST.mk_binder uu____3109 r
                 FStar_Parser_AST.Type_level None
           | uu____3111 ->
               let uu____3112 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3112
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3114 =
                    let uu____3115 =
                      let uu____3118 = bv_as_unique_ident x in
                      (uu____3118, e) in
                    FStar_Parser_AST.Annotated uu____3115 in
                  FStar_Parser_AST.mk_binder uu____3114 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3126 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3126 in
      let uu____3127 =
        let uu____3128 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3128.FStar_Syntax_Syntax.n in
      match uu____3127 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3134 = mk1 FStar_Parser_AST.PatWild in Some uu____3134
          else
            (let uu____3136 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3136
               (fun aq  ->
                  let uu____3142 =
                    let uu____3143 =
                      let uu____3144 =
                        let uu____3148 = bv_as_unique_ident x in
                        (uu____3148, aq) in
                      FStar_Parser_AST.PatVar uu____3144 in
                    mk1 uu____3143 in
                  Some uu____3142))
      | uu____3150 ->
          let uu____3151 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3151
            (fun aq  ->
               let pat =
                 let uu____3158 =
                   let uu____3159 =
                     let uu____3163 = bv_as_unique_ident x in
                     (uu____3163, aq) in
                   FStar_Parser_AST.PatVar uu____3159 in
                 mk1 uu____3158 in
               let uu____3165 = FStar_Options.print_bound_var_types () in
               if uu____3165
               then
                 let uu____3167 =
                   let uu____3168 =
                     let uu____3169 =
                       let uu____3172 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3172) in
                     FStar_Parser_AST.PatAscribed uu____3169 in
                   mk1 uu____3168 in
                 Some uu____3167
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
              (fun uu____3206  -> match uu____3206 with | (p2,b) -> aux p2)
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
              (fun uu____3225  -> match uu____3225 with | (p2,b) -> aux p2)
              args in
          let uu____3230 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3230
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3234;
             FStar_Syntax_Syntax.fv_delta = uu____3235;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3251 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3251 FStar_List.rev in
          let args1 =
            let uu____3260 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3269  ->
                      match uu____3269 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3260 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3311 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3311
            | (hd1::tl1,hd2::tl2) ->
                let uu____3325 = map21 tl1 tl2 in (hd1, hd2) :: uu____3325 in
          let args2 =
            let uu____3335 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3335 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3361  -> match uu____3361 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3368 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3368 with
           | Some (op,uu____3373) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3378 =
                 let uu____3379 =
                   let uu____3383 = bv_as_unique_ident v1 in
                   (uu____3383, None) in
                 FStar_Parser_AST.PatVar uu____3379 in
               mk1 uu____3378)
      | FStar_Syntax_Syntax.Pat_wild uu____3385 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3393 =
              let uu____3394 =
                let uu____3398 = bv_as_unique_ident bv in (uu____3398, None) in
              FStar_Parser_AST.PatVar uu____3394 in
            mk1 uu____3393 in
          let uu____3400 = FStar_Options.print_bound_var_types () in
          if uu____3400
          then
            let uu____3401 =
              let uu____3402 =
                let uu____3405 = resugar_term term in (pat, uu____3405) in
              FStar_Parser_AST.PatAscribed uu____3402 in
            mk1 uu____3401
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___193_3410  ->
    match uu___193_3410 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3416 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3417 -> None
    | FStar_Syntax_Syntax.Projector uu____3418 -> None
    | FStar_Syntax_Syntax.RecordType uu____3421 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3426 -> None
    | FStar_Syntax_Syntax.Action uu____3431 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___194_3434  ->
    match uu___194_3434 with
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
          (tylid,uvs,bs,t,uu____3456,datacons) ->
          let uu____3462 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3473,uu____3474,uu____3475,inductive_lid,uu____3477,uu____3478)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3481 -> failwith "unexpected")) in
          (match uu____3462 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3492 = FStar_Options.print_implicits () in
                 if uu____3492 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3499 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___195_3501  ->
                           match uu___195_3501 with
                           | FStar_Syntax_Syntax.RecordType uu____3502 ->
                               true
                           | uu____3507 -> false)) in
                 if uu____3499
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3535,univs1,term,uu____3538,num,uu____3540)
                         ->
                         let uu____3543 =
                           let uu____3544 = FStar_Syntax_Subst.compress term in
                           uu____3544.FStar_Syntax_Syntax.n in
                         (match uu____3543 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3553) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3584  ->
                                        match uu____3584 with
                                        | (b,qual) ->
                                            let uu____3593 =
                                              let uu____3594 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3594 in
                                            let uu____3595 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3593, uu____3595, None))) in
                              FStar_List.append mfields fields
                          | uu____3601 -> failwith "unexpected")
                     | uu____3607 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3674,num,uu____3676) ->
                          let c =
                            let uu____3686 =
                              let uu____3688 = resugar_term term in
                              Some uu____3688 in
                            ((l.FStar_Ident.ident), uu____3686, None, false) in
                          c :: constructors
                      | uu____3697 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3736 ->
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
        let uu____3750 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3750;
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
      let uu____3763 = ts in
      match uu____3763 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3769 =
            let uu____3770 =
              let uu____3777 =
                let uu____3782 =
                  let uu____3786 =
                    let uu____3787 =
                      let uu____3794 = resugar_term typ in
                      (name1, [], None, uu____3794) in
                    FStar_Parser_AST.TyconAbbrev uu____3787 in
                  (uu____3786, None) in
                [uu____3782] in
              (false, uu____3777) in
            FStar_Parser_AST.Tycon uu____3770 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3769
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
            let uu____3833 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3833 with
            | (bs,action_defn) ->
                let uu____3838 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3838 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3844 = FStar_Options.print_implicits () in
                       if uu____3844
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3848 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3848 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3857 =
                           let uu____3863 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3863,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3857 in
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
          let uu____3902 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____3902 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____3908 = FStar_Options.print_implicits () in
                if uu____3908 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____3912 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____3912 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3953) ->
        let uu____3958 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____3969 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____3978 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____3982 -> false
                  | uu____3990 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____3958 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4010 se1 =
               match uu____4010 with
               | (datacon_ses1,tycons) ->
                   let uu____4025 = resugar_typ datacon_ses1 se1 in
                   (match uu____4025 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4034 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4034 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4053 =
                         let uu____4054 =
                           let uu____4055 =
                             let uu____4062 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4062) in
                           FStar_Parser_AST.Tycon uu____4055 in
                         decl'_to_decl se uu____4054 in
                       Some uu____4053
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4079,uu____4080,uu____4081,uu____4082,uu____4083)
                            ->
                            let uu____4086 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4086
                        | uu____4088 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4090 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4094,attrs) ->
        let uu____4100 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_4102  ->
                  match uu___196_4102 with
                  | FStar_Syntax_Syntax.Projector (uu____4103,uu____4104) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4105 -> true
                  | uu____4106 -> false)) in
        if uu____4100
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4131) ->
               let uu____4138 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4138
           | uu____4142 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4145,fml) ->
        let uu____4147 =
          let uu____4148 =
            let uu____4149 =
              let uu____4152 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4152) in
            FStar_Parser_AST.Assume uu____4149 in
          decl'_to_decl se uu____4148 in
        Some uu____4147
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4154 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4154
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4156 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4156
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4163,t) ->
              let uu____4170 = resugar_term t in Some uu____4170
          | uu____4171 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4176,t) ->
              let uu____4183 = resugar_term t in Some uu____4183
          | uu____4184 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4199 -> failwith "Should not happen hopefully" in
        let uu____4204 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4204
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4212 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4212 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4219 = FStar_Options.print_implicits () in
               if uu____4219 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4225 =
               let uu____4226 =
                 let uu____4227 =
                   let uu____4234 =
                     let uu____4239 =
                       let uu____4243 =
                         let uu____4244 =
                           let uu____4251 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4251) in
                         FStar_Parser_AST.TyconAbbrev uu____4244 in
                       (uu____4243, None) in
                     [uu____4239] in
                   (false, uu____4234) in
                 FStar_Parser_AST.Tycon uu____4227 in
               decl'_to_decl se uu____4226 in
             Some uu____4225)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4266 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4266
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4270 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___197_4272  ->
                  match uu___197_4272 with
                  | FStar_Syntax_Syntax.Projector (uu____4273,uu____4274) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4275 -> true
                  | uu____4276 -> false)) in
        if uu____4270
        then None
        else
          (let uu____4279 =
             let uu____4280 =
               let uu____4281 =
                 let uu____4284 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4284) in
               FStar_Parser_AST.Val uu____4281 in
             decl'_to_decl se uu____4280 in
           Some uu____4279)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4285 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4294 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4302 -> None