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
       (fun uu___187_43  ->
          match uu___187_43 with
          | (uu____47,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____48)) -> false
          | uu____50 -> true))
let resugar_arg_qual:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
        if b
        then FStar_Pervasives_Native.None
        else
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
let rec universe_to_int:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____87 -> (n1, u)
let rec resugar_universe:
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____108 ->
          let uu____109 = universe_to_int (Prims.parse_int "0") u in
          (match uu____109 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____114 =
                      let uu____115 =
                        let uu____116 =
                          let uu____122 = FStar_Util.string_of_int n1 in
                          (uu____122, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____116 in
                      FStar_Parser_AST.Const uu____115 in
                    mk1 uu____114 r
                | uu____128 ->
                    let e1 =
                      let uu____130 =
                        let uu____131 =
                          let uu____132 =
                            let uu____138 = FStar_Util.string_of_int n1 in
                            (uu____138, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____132 in
                        FStar_Parser_AST.Const uu____131 in
                      mk1 uu____130 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____148 ->
               let t =
                 let uu____151 =
                   let uu____152 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____152 in
                 mk1 uu____151 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____158 =
                        let uu____159 =
                          let uu____163 = resugar_universe x r in
                          (acc, uu____163, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____159 in
                      mk1 uu____158 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____165 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____172 =
              let uu____175 =
                let uu____176 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____176 in
              (uu____175, r) in
            FStar_Ident.mk_ident uu____172 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___188_190 =
      match uu___188_190 with
      | "Amp" -> FStar_Pervasives_Native.Some ("&", (Prims.parse_int "0"))
      | "At" -> FStar_Pervasives_Native.Some ("@", (Prims.parse_int "0"))
      | "Plus" -> FStar_Pervasives_Native.Some ("+", (Prims.parse_int "0"))
      | "Minus" -> FStar_Pervasives_Native.Some ("-", (Prims.parse_int "0"))
      | "Subtraction" ->
          FStar_Pervasives_Native.Some ("-", (Prims.parse_int "2"))
      | "Slash" -> FStar_Pervasives_Native.Some ("/", (Prims.parse_int "0"))
      | "Less" -> FStar_Pervasives_Native.Some ("<", (Prims.parse_int "0"))
      | "Equals" -> FStar_Pervasives_Native.Some ("=", (Prims.parse_int "0"))
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", (Prims.parse_int "0"))
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", (Prims.parse_int "0"))
      | "Bar" -> FStar_Pervasives_Native.Some ("|", (Prims.parse_int "0"))
      | "Bang" -> FStar_Pervasives_Native.Some ("!", (Prims.parse_int "0"))
      | "Hat" -> FStar_Pervasives_Native.Some ("^", (Prims.parse_int "0"))
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", (Prims.parse_int "0"))
      | "Star" -> FStar_Pervasives_Native.Some ("*", (Prims.parse_int "0"))
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", (Prims.parse_int "0"))
      | "Colon" -> FStar_Pervasives_Native.Some (":", (Prims.parse_int "0"))
      | uu____228 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____242 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____248 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____248 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____257 ->
               let op =
                 let uu____260 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____281) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____260 in
               FStar_Pervasives_Native.Some (op, (Prims.parse_int "0")))
        else FStar_Pervasives_Native.None
let rec resugar_term_as_op:
  FStar_Syntax_Syntax.term ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Parser_Const.op_Addition, "+");
      (FStar_Parser_Const.op_Subtraction, "-");
      (FStar_Parser_Const.op_Minus, "-");
      (FStar_Parser_Const.op_Multiply, "*");
      (FStar_Parser_Const.op_Division, "/");
      (FStar_Parser_Const.op_Modulus, "%");
      (FStar_Parser_Const.read_lid, "!");
      (FStar_Parser_Const.list_append_lid, "@");
      (FStar_Parser_Const.list_tot_append_lid, "@");
      (FStar_Parser_Const.strcat_lid, "^");
      (FStar_Parser_Const.pipe_right_lid, "|>");
      (FStar_Parser_Const.pipe_left_lid, "<|");
      (FStar_Parser_Const.op_Eq, "=");
      (FStar_Parser_Const.op_ColonEq, ":=");
      (FStar_Parser_Const.op_notEq, "<>");
      (FStar_Parser_Const.not_lid, "~");
      (FStar_Parser_Const.op_And, "&&");
      (FStar_Parser_Const.op_Or, "||");
      (FStar_Parser_Const.op_LTE, "<=");
      (FStar_Parser_Const.op_GTE, ">=");
      (FStar_Parser_Const.op_LT, "<");
      (FStar_Parser_Const.op_GT, ">");
      (FStar_Parser_Const.op_Modulus, "mod");
      (FStar_Parser_Const.and_lid, "/\\");
      (FStar_Parser_Const.or_lid, "\\/");
      (FStar_Parser_Const.imp_lid, "==>");
      (FStar_Parser_Const.iff_lid, "<==>");
      (FStar_Parser_Const.precedes_lid, "<<");
      (FStar_Parser_Const.eq2_lid, "==");
      (FStar_Parser_Const.eq3_lid, "===");
      (FStar_Parser_Const.forall_lid, "forall");
      (FStar_Parser_Const.exists_lid, "exists");
      (FStar_Parser_Const.salloc_lid, "alloc")] in
    let fallback fv =
      let uu____380 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____380 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____406 ->
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
          then FStar_Pervasives_Native.Some ("dtuple", (Prims.parse_int "0"))
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some ("tuple", (Prims.parse_int "0"))
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", (Prims.parse_int "0"))
              else
                (let uu____443 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____443
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____452 =
      let uu____453 = FStar_Syntax_Subst.compress t in
      uu____453.FStar_Syntax_Syntax.n in
    match uu____452 with
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
        let uu____475 = string_to_op s in
        (match uu____475 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____489 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____499 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____506 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____511 -> true
    | uu____512 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____540 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____540 in
    let var a r =
      let uu____548 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____548 in
    let uu____549 =
      let uu____550 = FStar_Syntax_Subst.compress t in
      uu____550.FStar_Syntax_Syntax.n in
    match uu____549 with
    | FStar_Syntax_Syntax.Tm_delayed uu____553 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____570 = let uu____572 = bv_as_unique_ident x in [uu____572] in
          FStar_Ident.lid_of_ids uu____570 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____575 = let uu____577 = bv_as_unique_ident x in [uu____577] in
          FStar_Ident.lid_of_ids uu____575 in
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
          let uu____601 =
            let uu____602 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____602 in
          mk1 uu____601
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
             | uu____615 -> failwith "wrong projector format")
          else
            (let uu____618 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____621 =
                    let uu____622 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____622 in
                  let uu____623 = FStar_String.get s (Prims.parse_int "0") in
                  uu____621 <> uu____623) in
             if uu____618
             then
               let uu____624 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____624
             else
               (let uu____626 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____626))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____633 = FStar_Options.print_universes () in
        if uu____633
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____640 =
                   let uu____641 =
                     let uu____645 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____645, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____641 in
                 mk1 uu____640) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____648 = FStar_Syntax_Syntax.is_teff t in
        if uu____648
        then
          let uu____649 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____649
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____652 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____652
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____653 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____653
         | uu____654 ->
             let uu____655 = FStar_Options.print_universes () in
             if uu____655
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____666 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____666))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____669) ->
        let uu____682 = FStar_Syntax_Subst.open_term xs body in
        (match uu____682 with
         | (xs1,body1) ->
             let xs2 =
               let uu____688 = FStar_Options.print_implicits () in
               if uu____688 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____698  ->
                       match uu____698 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____718 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____718 with
         | (xs1,body1) ->
             let xs2 =
               let uu____724 = FStar_Options.print_implicits () in
               if uu____724 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____729 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____729 FStar_List.rev in
             let rec aux body3 uu___189_743 =
               match uu___189_743 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____756 =
          let uu____759 =
            let uu____760 = FStar_Syntax_Syntax.mk_binder x in [uu____760] in
          FStar_Syntax_Subst.open_term uu____759 phi in
        (match uu____756 with
         | (x1,phi1) ->
             let b =
               let uu____764 = FStar_List.hd x1 in
               resugar_binder uu____764 t.FStar_Syntax_Syntax.pos in
             let uu____767 =
               let uu____768 =
                 let uu____771 = resugar_term phi1 in (b, uu____771) in
               FStar_Parser_AST.Refine uu____768 in
             mk1 uu____767)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___190_801 =
          match uu___190_801 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____848 -> failwith "last of an empty list" in
        let rec last_two uu___191_872 =
          match uu___191_872 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____892::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____944::t1 -> last_two t1 in
        let rec last_three uu___192_972 =
          match uu___192_972 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____992::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1010::uu____1011::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1084::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1123  ->
                    match uu____1123 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1139 = FStar_Options.print_implicits () in
          if uu____1139 then args else filter_imp args in
        let uu____1148 = resugar_term_as_op e in
        (match uu____1148 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1154) ->
             (match args1 with
              | (fst1,uu____1158)::(snd1,uu____1160)::rest ->
                  let e1 =
                    let uu____1184 =
                      let uu____1185 =
                        let uu____1189 =
                          let uu____1191 = resugar_term fst1 in
                          let uu____1192 =
                            let uu____1194 = resugar_term snd1 in
                            [uu____1194] in
                          uu____1191 :: uu____1192 in
                        ((FStar_Ident.id_of_text "*"), uu____1189) in
                      FStar_Parser_AST.Op uu____1185 in
                    mk1 uu____1184 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1204  ->
                         match uu____1204 with
                         | (x,uu____1208) ->
                             let uu____1209 =
                               let uu____1210 =
                                 let uu____1214 =
                                   let uu____1216 =
                                     let uu____1218 = resugar_term x in
                                     [uu____1218] in
                                   e1 :: uu____1216 in
                                 ((FStar_Ident.id_of_text "*"), uu____1214) in
                               FStar_Parser_AST.Op uu____1210 in
                             mk1 uu____1209) e1 rest
              | uu____1220 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1226) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1251)::[] -> b
               | uu____1264 -> failwith "wrong arguments to dtuple" in
             let uu____1272 =
               let uu____1273 = FStar_Syntax_Subst.compress body in
               uu____1273.FStar_Syntax_Syntax.n in
             (match uu____1272 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1278) ->
                  let uu____1291 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1291 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1297 = FStar_Options.print_implicits () in
                         if uu____1297 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1306 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1320  ->
                            match uu____1320 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1330) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____1334) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____1337 = FStar_List.hd args1 in
             (match uu____1337 with
              | (t1,uu____1347) ->
                  let uu____1352 =
                    let uu____1353 = FStar_Syntax_Subst.compress t1 in
                    uu____1353.FStar_Syntax_Syntax.n in
                  (match uu____1352 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1358 =
                         let uu____1359 =
                           let uu____1362 = resugar_term t1 in
                           (uu____1362, f) in
                         FStar_Parser_AST.Project uu____1359 in
                       mk1 uu____1358
                   | uu____1363 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____1364) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1383 =
               match new_args with
               | (a1,uu____1397)::(a2,uu____1399)::[] -> (a1, a2)
               | uu____1424 -> failwith "wrong arguments to try_with" in
             (match uu____1383 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1450 =
                      let uu____1451 = FStar_Syntax_Subst.compress term in
                      uu____1451.FStar_Syntax_Syntax.n in
                    match uu____1450 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1456) ->
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
         | FStar_Pervasives_Native.Some ("try_with",uu____1573) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____1577) when
             (op = "forall") || (op = "exists") ->
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
                   let uu____1655 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1655 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1661 = FStar_Options.print_implicits () in
                          if uu____1661 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1668 =
                          let uu____1673 =
                            let uu____1674 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1674.FStar_Syntax_Syntax.n in
                          match uu____1673 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1718  ->
                                                 match uu____1718 with
                                                 | (e2,uu____1722) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1725) ->
                                    let uu____1726 =
                                      let uu____1728 =
                                        let uu____1729 = name s r in
                                        mk1 uu____1729 in
                                      [uu____1728] in
                                    [uu____1726]
                                | uu____1732 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1737 ->
                              let uu____1738 = resugar_term body2 in
                              ([], uu____1738) in
                        (match uu____1668 with
                         | (pats,body3) ->
                             let uu____1748 = uncurry xs3 pats body3 in
                             (match uu____1748 with
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
               | uu____1775 ->
                   if op = "forall"
                   then
                     let uu____1776 =
                       let uu____1777 =
                         let uu____1784 = resugar_term body in
                         ([], [[]], uu____1784) in
                       FStar_Parser_AST.QForall uu____1777 in
                     mk1 uu____1776
                   else
                     (let uu____1791 =
                        let uu____1792 =
                          let uu____1799 = resugar_term body in
                          ([], [[]], uu____1799) in
                        FStar_Parser_AST.QExists uu____1792 in
                      mk1 uu____1791) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1822)::[] -> resugar b
                | uu____1835 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____1842) ->
             let uu____1845 = FStar_List.hd args1 in
             (match uu____1845 with | (e1,uu____1855) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1885  ->
                       match uu____1885 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____1890 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1890 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1901 =
                         let uu____1902 =
                           let uu____1906 =
                             let uu____1908 = last1 args1 in
                             resugar uu____1908 in
                           (op1, uu____1906) in
                         FStar_Parser_AST.Op uu____1902 in
                       mk1 uu____1901
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1923 =
                         let uu____1924 =
                           let uu____1928 =
                             let uu____1930 = last_two args1 in
                             resugar uu____1930 in
                           (op1, uu____1928) in
                         FStar_Parser_AST.Op uu____1924 in
                       mk1 uu____1923
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1945 =
                         let uu____1946 =
                           let uu____1950 =
                             let uu____1952 = last_three args1 in
                             resugar uu____1952 in
                           (op1, uu____1950) in
                         FStar_Parser_AST.Op uu____1946 in
                       mk1 uu____1945
                   | uu____1957 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1968 =
                    let uu____1969 =
                      let uu____1973 =
                        let uu____1975 = last_two args1 in resugar uu____1975 in
                      (op1, uu____1973) in
                    FStar_Parser_AST.Op uu____1969 in
                  mk1 uu____1968
              | uu____1980 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1983,t1)::[]) ->
        let bnds =
          let uu____2033 =
            let uu____2036 = resugar_pat pat in
            let uu____2037 = resugar_term e in (uu____2036, uu____2037) in
          [uu____2033] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2048,t1)::(pat2,uu____2051,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2118 =
          let uu____2119 =
            let uu____2123 = resugar_term e in
            let uu____2124 = resugar_term t1 in
            let uu____2125 = resugar_term t2 in
            (uu____2123, uu____2124, uu____2125) in
          FStar_Parser_AST.If uu____2119 in
        mk1 uu____2118
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2163 =
          match uu____2163 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____2182 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____2182 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2185 =
          let uu____2186 =
            let uu____2194 = resugar_term e in
            let uu____2195 = FStar_List.map resugar_branch branches in
            (uu____2194, uu____2195) in
          FStar_Parser_AST.Match uu____2186 in
        mk1 uu____2185
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2217) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2270 =
          let uu____2271 =
            let uu____2276 = resugar_term e in (uu____2276, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2271 in
        mk1 uu____2270
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2294 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2294 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2310 =
                 let uu____2313 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2313 in
               match uu____2310 with
               | (univs1,td) ->
                   let uu____2320 =
                     let uu____2327 =
                       let uu____2328 = FStar_Syntax_Subst.compress td in
                       uu____2328.FStar_Syntax_Syntax.n in
                     match uu____2327 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2337,(t1,uu____2339)::(d,uu____2341)::[]) ->
                         (t1, d)
                     | uu____2375 -> failwith "wrong let binding format" in
                   (match uu____2320 with
                    | (typ,def) ->
                        let uu____2396 =
                          let uu____2400 =
                            let uu____2401 = FStar_Syntax_Subst.compress def in
                            uu____2401.FStar_Syntax_Syntax.n in
                          match uu____2400 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2409) ->
                              let uu____2422 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2422 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2431 =
                                       FStar_Options.print_implicits () in
                                     if uu____2431 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2433 -> ([], def, false) in
                        (match uu____2396 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2454 =
                                 FStar_Options.print_universes () in
                               if uu____2454
                               then
                                 let uu____2455 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2455
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2461 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2468 =
                                     let uu____2469 =
                                       let uu____2470 =
                                         let uu____2474 =
                                           bv_as_unique_ident bv in
                                         (uu____2474,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____2470 in
                                     mk_pat uu____2469 in
                                   (uu____2468, term) in
                             (match uu____2461 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2495  ->
                                              match uu____2495 with
                                              | (bv,uu____2499) ->
                                                  let uu____2500 =
                                                    let uu____2501 =
                                                      let uu____2505 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2505,
                                                        FStar_Pervasives_Native.None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2501 in
                                                  mk_pat uu____2500)) in
                                    let uu____2507 =
                                      let uu____2510 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2510) in
                                    let uu____2512 =
                                      universe_to_string univs1 in
                                    (uu____2507, uu____2512)
                                  else
                                    (let uu____2516 =
                                       let uu____2519 = resugar_term term1 in
                                       (pat, uu____2519) in
                                     let uu____2520 =
                                       universe_to_string univs1 in
                                     (uu____2516, uu____2520))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives_Native.fst r in
             let comments = FStar_List.map FStar_Pervasives_Native.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2559) ->
        let s =
          let uu____2577 =
            let uu____2578 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2578 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2577 in
        let uu____2579 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2579
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___193_2589 =
          match uu___193_2589 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2590 =
                let uu____2591 = FStar_Syntax_Subst.compress e in
                uu____2591.FStar_Syntax_Syntax.n in
              (match uu____2590 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2617 =
                       let uu____2618 = FStar_Syntax_Subst.compress h in
                       uu____2618.FStar_Syntax_Syntax.n in
                     match uu____2617 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2625 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2625, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2633 = aux h1 in
                         (match uu____2633 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2645 -> failwith "wrong Data_app head format" in
                   let uu____2649 = aux head1 in
                   (match uu____2649 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2666 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2666, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2679  ->
                               match uu____2679 with
                               | (t1,uu____2685) ->
                                   let uu____2686 = resugar_term t1 in
                                   (uu____2686, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2687 =
                          FStar_Parser_Const.is_tuple_data_lid' head2 in
                        if uu____2687
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2692 = FStar_Options.print_universes () in
                           if uu____2692
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2702,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2708,uu____2709) -> resugar_term e
                    | uu____2714 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2715 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2721,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2737 =
                      let uu____2738 =
                        let uu____2743 = resugar_seq t11 in
                        (uu____2743, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2738 in
                    mk1 uu____2737
                | uu____2745 -> t1 in
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
               | uu____2758 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____2760 =
                let uu____2761 = FStar_Syntax_Subst.compress e in
                uu____2761.FStar_Syntax_Syntax.n in
              (match uu____2760 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2765;
                      FStar_Syntax_Syntax.pos = uu____2766;
                      FStar_Syntax_Syntax.vars = uu____2767;_},(term,uu____2769)::[])
                   -> resugar_term term
               | uu____2791 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2816  ->
                       match uu____2816 with
                       | (x,uu____2820) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2822,p) ->
             let uu____2824 =
               let uu____2825 =
                 let uu____2829 = resugar_term e in (uu____2829, l, p) in
               FStar_Parser_AST.Labeled uu____2825 in
             mk1 uu____2824
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____2831,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2840 =
               let uu____2841 =
                 let uu____2846 = resugar_term e in
                 let uu____2847 =
                   let uu____2848 =
                     let uu____2849 =
                       let uu____2855 =
                         let uu____2859 =
                           let uu____2862 = resugar_term t1 in
                           (uu____2862, FStar_Parser_AST.Nothing) in
                         [uu____2859] in
                       (name1, uu____2855) in
                     FStar_Parser_AST.Construct uu____2849 in
                   mk1 uu____2848 in
                 (uu____2846, uu____2847, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2841 in
             mk1 uu____2840
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2872,t1) ->
             let uu____2878 =
               let uu____2879 =
                 let uu____2884 = resugar_term e in
                 let uu____2885 =
                   let uu____2886 =
                     let uu____2887 =
                       let uu____2893 =
                         let uu____2897 =
                           let uu____2900 = resugar_term t1 in
                           (uu____2900, FStar_Parser_AST.Nothing) in
                         [uu____2897] in
                       (name1, uu____2893) in
                     FStar_Parser_AST.Construct uu____2887 in
                   mk1 uu____2886 in
                 (uu____2884, uu____2885, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2879 in
             mk1 uu____2878)
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
         | FStar_Pervasives_Native.None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Parser_Const.effect_Tot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | FStar_Pervasives_Native.Some u1 ->
             let uu____2931 = FStar_Options.print_universes () in
             if uu____2931
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.GTotal (typ,u) ->
        let t = resugar_term typ in
        (match u with
         | FStar_Pervasives_Native.None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Parser_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | FStar_Pervasives_Native.Some u1 ->
             let uu____2967 = FStar_Options.print_universes () in
             if uu____2967
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.Comp c1 ->
        let result =
          let uu____2990 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2990, FStar_Parser_AST.Nothing) in
        let uu____2991 = FStar_Options.print_effect_args () in
        if uu____2991
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___194_3032 =
                match uu___194_3032 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3074 -> aux l tl1
                     | uu____3079 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3103  ->
                 match uu____3103 with
                 | (e,uu____3109) ->
                     let uu____3110 = resugar_term e in
                     (uu____3110, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___195_3124 =
            match uu___195_3124 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3144 = resugar_term e in
                       (uu____3144, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3147 -> aux l tl1) in
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
      let uu____3171 = b in
      match uu____3171 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3175 =
                 let uu____3176 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3176 in
               FStar_Parser_AST.mk_binder uu____3175 r
                 FStar_Parser_AST.Type_level FStar_Pervasives_Native.None
           | uu____3177 ->
               let uu____3178 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3178
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level FStar_Pervasives_Native.None
               else
                 (let uu____3180 =
                    let uu____3181 =
                      let uu____3184 = bv_as_unique_ident x in
                      (uu____3184, e) in
                    FStar_Parser_AST.Annotated uu____3181 in
                  FStar_Parser_AST.mk_binder uu____3180 r
                    FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3192 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3192 in
      let uu____3193 =
        let uu____3194 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3194.FStar_Syntax_Syntax.n in
      match uu____3193 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3200 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____3200
          else
            (let uu____3202 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3202
               (fun aq  ->
                  let uu____3210 =
                    let uu____3211 =
                      let uu____3212 =
                        let uu____3216 = bv_as_unique_ident x in
                        (uu____3216, aq) in
                      FStar_Parser_AST.PatVar uu____3212 in
                    mk1 uu____3211 in
                  FStar_Pervasives_Native.Some uu____3210))
      | uu____3218 ->
          let uu____3219 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3219
            (fun aq  ->
               let pat =
                 let uu____3230 =
                   let uu____3231 =
                     let uu____3235 = bv_as_unique_ident x in
                     (uu____3235, aq) in
                   FStar_Parser_AST.PatVar uu____3231 in
                 mk1 uu____3230 in
               let uu____3237 = FStar_Options.print_bound_var_types () in
               if uu____3237
               then
                 let uu____3239 =
                   let uu____3240 =
                     let uu____3241 =
                       let uu____3244 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3244) in
                     FStar_Parser_AST.PatAscribed uu____3241 in
                   mk1 uu____3240 in
                 FStar_Pervasives_Native.Some uu____3239
               else FStar_Pervasives_Native.Some pat)
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
            FStar_Parser_Const.cons_lid
          ->
          let args1 =
            FStar_List.map
              (fun uu____3281  -> match uu____3281 with | (p2,b) -> aux p2)
              args in
          mk1 (FStar_Parser_AST.PatList args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          (FStar_Parser_Const.is_tuple_data_lid'
             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
            ||
            (FStar_Parser_Const.is_dtuple_data_lid'
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
          ->
          let args1 =
            FStar_List.map
              (fun uu____3303  -> match uu____3303 with | (p2,b) -> aux p2)
              args in
          let uu____3308 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3308
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3312;
             FStar_Syntax_Syntax.fv_delta = uu____3313;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3329 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3329 FStar_List.rev in
          let args1 =
            let uu____3339 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3351  ->
                      match uu____3351 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3339 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3393 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3393
            | (hd1::tl1,hd2::tl2) ->
                let uu____3407 = map21 tl1 tl2 in (hd1, hd2) :: uu____3407 in
          let args2 =
            let uu____3417 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3417 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3446  -> match uu____3446 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3453 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3453 with
           | FStar_Pervasives_Native.Some (op,uu____3458) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____3463 =
                 let uu____3464 =
                   let uu____3468 = bv_as_unique_ident v1 in
                   (uu____3468, FStar_Pervasives_Native.None) in
                 FStar_Parser_AST.PatVar uu____3464 in
               mk1 uu____3463)
      | FStar_Syntax_Syntax.Pat_wild uu____3470 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3478 =
              let uu____3479 =
                let uu____3483 = bv_as_unique_ident bv in
                (uu____3483, FStar_Pervasives_Native.None) in
              FStar_Parser_AST.PatVar uu____3479 in
            mk1 uu____3478 in
          let uu____3485 = FStar_Options.print_bound_var_types () in
          if uu____3485
          then
            let uu____3486 =
              let uu____3487 =
                let uu____3490 = resugar_term term in (pat, uu____3490) in
              FStar_Parser_AST.PatAscribed uu____3487 in
            mk1 uu____3486
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___196_3496  ->
    match uu___196_3496 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Visible
    | FStar_Syntax_Syntax.Irreducible  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Logic
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____3502 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3503 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____3504 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____3507 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____3512 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____3517 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___197_3521  ->
    match uu___197_3521 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
let resugar_typ:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelts,FStar_Parser_AST.tycon)
        FStar_Pervasives_Native.tuple2
  =
  fun datacon_ses  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tylid,uvs,bs,t,uu____3543,datacons) ->
          let uu____3549 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3567,uu____3568,uu____3569,inductive_lid,uu____3571,uu____3572)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3575 -> failwith "unexpected")) in
          (match uu____3549 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3587 = FStar_Options.print_implicits () in
                 if uu____3587 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3595 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___198_3599  ->
                           match uu___198_3599 with
                           | FStar_Syntax_Syntax.RecordType uu____3600 ->
                               true
                           | uu____3605 -> false)) in
                 if uu____3595
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3633,univs1,term,uu____3636,num,uu____3638)
                         ->
                         let uu____3641 =
                           let uu____3642 = FStar_Syntax_Subst.compress term in
                           uu____3642.FStar_Syntax_Syntax.n in
                         (match uu____3641 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3651) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3687  ->
                                        match uu____3687 with
                                        | (b,qual) ->
                                            let uu____3696 =
                                              let uu____3697 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3697 in
                                            let uu____3698 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3696, uu____3698,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____3704 -> failwith "unexpected")
                     | uu____3710 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2,
                       FStar_Pervasives_Native.None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3777,num,uu____3779) ->
                          let c =
                            let uu____3789 =
                              let uu____3791 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____3791 in
                            ((l.FStar_Ident.ident), uu____3789,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____3800 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____3839 ->
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
        let uu____3856 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____3856;
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
      let uu____3873 = ts in
      match uu____3873 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3879 =
            let uu____3880 =
              let uu____3887 =
                let uu____3892 =
                  let uu____3896 =
                    let uu____3897 =
                      let uu____3904 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____3904) in
                    FStar_Parser_AST.TyconAbbrev uu____3897 in
                  (uu____3896, FStar_Pervasives_Native.None) in
                [uu____3892] in
              (false, uu____3887) in
            FStar_Parser_AST.Tycon uu____3880 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3879
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
            let uu____3948 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3948 with
            | (bs,action_defn) ->
                let uu____3953 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3953 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3959 = FStar_Options.print_implicits () in
                       if uu____3959
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3963 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3963 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3973 =
                           let uu____3979 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3979,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3973 in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un in
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2,
                                     FStar_Pervasives_Native.None, t)),
                                 FStar_Pervasives_Native.None)]))
                     else
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2,
                                     FStar_Pervasives_Native.None,
                                     action_defn1)),
                                 FStar_Pervasives_Native.None)]))) in
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident in
          let uu____4018 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4018 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4024 = FStar_Options.print_implicits () in
                if uu____4024 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4028 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4028 FStar_List.rev in
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
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4071) ->
        let uu____4076 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4089 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4098 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4102 -> false
                  | uu____4110 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4076 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4130 se1 =
               match uu____4130 with
               | (datacon_ses1,tycons) ->
                   let uu____4145 = resugar_typ datacon_ses1 se1 in
                   (match uu____4145 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4154 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4154 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4173 =
                         let uu____4174 =
                           let uu____4175 =
                             let uu____4182 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____4182) in
                           FStar_Parser_AST.Tycon uu____4175 in
                         decl'_to_decl se uu____4174 in
                       FStar_Pervasives_Native.Some uu____4173
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4200,uu____4201,uu____4202,uu____4203,uu____4204)
                            ->
                            let uu____4207 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____4207
                        | uu____4209 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4211 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4215,attrs) ->
        let uu____4221 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___199_4226  ->
                  match uu___199_4226 with
                  | FStar_Syntax_Syntax.Projector (uu____4227,uu____4228) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4229 -> true
                  | uu____4230 -> false)) in
        if uu____4221
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4255) ->
               let uu____4262 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____4262
           | uu____4266 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4269,fml) ->
        let uu____4271 =
          let uu____4272 =
            let uu____4273 =
              let uu____4276 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4276) in
            FStar_Parser_AST.Assume uu____4273 in
          decl'_to_decl se uu____4272 in
        FStar_Pervasives_Native.Some uu____4271
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4278 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4278
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4280 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4280
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____4287,t) ->
              let uu____4294 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4294
          | uu____4295 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____4300,t) ->
              let uu____4307 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4307
          | uu____4308 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____4323 -> failwith "Should not happen hopefully" in
        let uu____4328 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____4328
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4336 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4336 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4343 = FStar_Options.print_implicits () in
               if uu____4343 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4350 =
               let uu____4351 =
                 let uu____4352 =
                   let uu____4359 =
                     let uu____4364 =
                       let uu____4368 =
                         let uu____4369 =
                           let uu____4376 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____4376) in
                         FStar_Parser_AST.TyconAbbrev uu____4369 in
                       (uu____4368, FStar_Pervasives_Native.None) in
                     [uu____4364] in
                   (false, uu____4359) in
                 FStar_Parser_AST.Tycon uu____4352 in
               decl'_to_decl se uu____4351 in
             FStar_Pervasives_Native.Some uu____4350)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4391 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____4391
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4395 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___200_4400  ->
                  match uu___200_4400 with
                  | FStar_Syntax_Syntax.Projector (uu____4401,uu____4402) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4403 -> true
                  | uu____4404 -> false)) in
        if uu____4395
        then FStar_Pervasives_Native.None
        else
          (let uu____4407 =
             let uu____4408 =
               let uu____4409 =
                 let uu____4412 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4412) in
               FStar_Parser_AST.Val uu____4409 in
             decl'_to_decl se uu____4408 in
           FStar_Pervasives_Native.Some uu____4407)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4413 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____4422 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____4430 -> FStar_Pervasives_Native.None