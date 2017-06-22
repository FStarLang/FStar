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
          | (uu____41,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____42)) -> false
          | uu____44 -> true))
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
      | uu____78 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____84 = FStar_Options.print_universes () in
    if uu____84
    then
      let uu____85 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____85 (FStar_String.concat ", ")
    else ""
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
                      let uu____155 =
                        let uu____156 =
                          let uu____160 = resugar_universe x r in
                          (acc, uu____160, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____156 in
                      mk1 uu____155 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____162 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____167 =
              let uu____170 =
                let uu____171 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____171 in
              (uu____170, r) in
            FStar_Ident.mk_ident uu____167 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___184_184 =
      match uu___184_184 with
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
      | uu____222 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____236 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____242 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____242 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____249 ->
               let op =
                 let uu____252 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____269) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____252 in
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
      let uu____367 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____367 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____392 ->
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
                (let uu____435 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____435
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____448 =
      let uu____449 = FStar_Syntax_Subst.compress t in
      uu____449.FStar_Syntax_Syntax.n in
    match uu____448 with
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
        let uu____477 = string_to_op s in
        (match uu____477 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____491 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____501 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____507 -> false
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
          let uu____576 = let uu____578 = bv_as_unique_ident x in [uu____578] in
          FStar_Ident.lid_of_ids uu____576 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____581 = let uu____583 = bv_as_unique_ident x in [uu____583] in
          FStar_Ident.lid_of_ids uu____581 in
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
          let uu____607 =
            let uu____608 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____608 in
          mk1 uu____607
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
             | uu____619 -> failwith "wrong projector format")
          else
            (let uu____622 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____623 =
                    let uu____624 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____624 in
                  let uu____625 = FStar_String.get s (Prims.parse_int "0") in
                  uu____623 <> uu____625) in
             if uu____622
             then
               let uu____626 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____626
             else
               (let uu____628 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____628))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____635 = FStar_Options.print_universes () in
        if uu____635
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____639 =
                   let uu____640 =
                     let uu____644 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____644, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____640 in
                 mk1 uu____639) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____647 = FStar_Syntax_Syntax.is_teff t in
        if uu____647
        then
          let uu____648 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____648
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____651 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____651
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____652 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____652
         | uu____653 ->
             let uu____654 = FStar_Options.print_universes () in
             if uu____654
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____665 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____665))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____668) ->
        let uu____691 = FStar_Syntax_Subst.open_term xs body in
        (match uu____691 with
         | (xs1,body1) ->
             let xs2 =
               let uu____697 = FStar_Options.print_implicits () in
               if uu____697 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____704  ->
                       match uu____704 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____724 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____724 with
         | (xs1,body1) ->
             let xs2 =
               let uu____730 = FStar_Options.print_implicits () in
               if uu____730 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____735 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____735 FStar_List.rev in
             let rec aux body3 uu___185_748 =
               match uu___185_748 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____761 =
          let uu____764 =
            let uu____765 = FStar_Syntax_Syntax.mk_binder x in [uu____765] in
          FStar_Syntax_Subst.open_term uu____764 phi in
        (match uu____761 with
         | (x1,phi1) ->
             let b =
               let uu____769 = FStar_List.hd x1 in
               resugar_binder uu____769 t.FStar_Syntax_Syntax.pos in
             let uu____772 =
               let uu____773 =
                 let uu____776 = resugar_term phi1 in (b, uu____776) in
               FStar_Parser_AST.Refine uu____773 in
             mk1 uu____772)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___186_806 =
          match uu___186_806 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____853 -> failwith "last of an empty list" in
        let rec last_two uu___187_877 =
          match uu___187_877 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____897::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____949::t1 -> last_two t1 in
        let rec last_three uu___188_977 =
          match uu___188_977 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____997::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1015::uu____1016::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1089::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1125  ->
                    match uu____1125 with | (e2,qual) -> resugar_term e2)) in
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
                       fun uu____1199  ->
                         match uu____1199 with
                         | (x,uu____1203) ->
                             let uu____1204 =
                               let uu____1205 =
                                 let uu____1209 =
                                   let uu____1211 =
                                     let uu____1213 = resugar_term x in
                                     [uu____1213] in
                                   e1 :: uu____1211 in
                                 ((FStar_Ident.id_of_text "*"), uu____1209) in
                               FStar_Parser_AST.Op uu____1205 in
                             mk1 uu____1204) e1 rest
              | uu____1215 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1221) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1243)::[] -> b
               | uu____1256 -> failwith "wrong arguments to dtuple" in
             let uu____1264 =
               let uu____1265 = FStar_Syntax_Subst.compress body in
               uu____1265.FStar_Syntax_Syntax.n in
             (match uu____1264 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1270) ->
                  let uu____1293 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1293 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1299 = FStar_Options.print_implicits () in
                         if uu____1299 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1307 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1318  ->
                            match uu____1318 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1326) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____1330) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____1333 = FStar_List.hd args1 in
             (match uu____1333 with
              | (t1,uu____1343) ->
                  let uu____1348 =
                    let uu____1349 = FStar_Syntax_Subst.compress t1 in
                    uu____1349.FStar_Syntax_Syntax.n in
                  (match uu____1348 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1362 =
                         let uu____1363 =
                           let uu____1366 = resugar_term t1 in
                           (uu____1366, f) in
                         FStar_Parser_AST.Project uu____1363 in
                       mk1 uu____1362
                   | uu____1367 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____1368) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1384 =
               match new_args with
               | (a1,uu____1398)::(a2,uu____1400)::[] -> (a1, a2)
               | uu____1425 -> failwith "wrong arguments to try_with" in
             (match uu____1384 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1451 =
                      let uu____1452 = FStar_Syntax_Subst.compress term in
                      uu____1452.FStar_Syntax_Syntax.n in
                    match uu____1451 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1457) ->
                        let uu____1480 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1480 with | (x1,e2) -> e2)
                    | uu____1485 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1487 = decomp body in resugar_term uu____1487 in
                  let handler1 =
                    let uu____1489 = decomp handler in
                    resugar_term uu____1489 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1495,uu____1496,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1513,uu____1514,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1527 =
                          let uu____1528 =
                            let uu____1533 = resugar_body t11 in
                            (uu____1533, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1528 in
                        mk1 uu____1527
                    | uu____1535 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1568 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____1584) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____1588) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1639 -> (xs, pat, t1) in
             let resugar body =
               let uu____1647 =
                 let uu____1648 = FStar_Syntax_Subst.compress body in
                 uu____1648.FStar_Syntax_Syntax.n in
               match uu____1647 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1653) ->
                   let uu____1676 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1676 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1682 = FStar_Options.print_implicits () in
                          if uu____1682 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1688 =
                          let uu____1693 =
                            let uu____1694 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1694.FStar_Syntax_Syntax.n in
                          match uu____1693 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1734  ->
                                                 match uu____1734 with
                                                 | (e2,uu____1738) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1741) ->
                                    let uu____1742 =
                                      let uu____1744 =
                                        let uu____1745 = name s r in
                                        mk1 uu____1745 in
                                      [uu____1744] in
                                    [uu____1742]
                                | uu____1748 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1753 ->
                              let uu____1754 = resugar_term body2 in
                              ([], uu____1754) in
                        (match uu____1688 with
                         | (pats,body3) ->
                             let uu____1764 = uncurry xs3 pats body3 in
                             (match uu____1764 with
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
               | uu____1791 ->
                   if op = "forall"
                   then
                     let uu____1792 =
                       let uu____1793 =
                         let uu____1800 = resugar_term body in
                         ([], [[]], uu____1800) in
                       FStar_Parser_AST.QForall uu____1793 in
                     mk1 uu____1792
                   else
                     (let uu____1807 =
                        let uu____1808 =
                          let uu____1815 = resugar_term body in
                          ([], [[]], uu____1815) in
                        FStar_Parser_AST.QExists uu____1808 in
                      mk1 uu____1807) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1835)::[] -> resugar b
                | uu____1848 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____1855) ->
             let uu____1858 = FStar_List.hd args1 in
             (match uu____1858 with | (e1,uu____1868) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1895  ->
                       match uu____1895 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1900 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1900 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1908 =
                         let uu____1909 =
                           let uu____1913 =
                             let uu____1915 = last1 args1 in
                             resugar uu____1915 in
                           (op1, uu____1913) in
                         FStar_Parser_AST.Op uu____1909 in
                       mk1 uu____1908
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1927 =
                         let uu____1928 =
                           let uu____1932 =
                             let uu____1934 = last_two args1 in
                             resugar uu____1934 in
                           (op1, uu____1932) in
                         FStar_Parser_AST.Op uu____1928 in
                       mk1 uu____1927
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1946 =
                         let uu____1947 =
                           let uu____1951 =
                             let uu____1953 = last_three args1 in
                             resugar uu____1953 in
                           (op1, uu____1951) in
                         FStar_Parser_AST.Op uu____1947 in
                       mk1 uu____1946
                   | uu____1958 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1966 =
                    let uu____1967 =
                      let uu____1971 =
                        let uu____1973 = last_two args1 in resugar uu____1973 in
                      (op1, uu____1971) in
                    FStar_Parser_AST.Op uu____1967 in
                  mk1 uu____1966
              | uu____1978 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1981,t1)::[]) ->
        let bnds =
          let uu____2036 =
            let uu____2039 = resugar_pat pat in
            let uu____2040 = resugar_term e in (uu____2039, uu____2040) in
          [uu____2036] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2051,t1)::(pat2,uu____2054,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2129 =
          let uu____2130 =
            let uu____2134 = resugar_term e in
            let uu____2135 = resugar_term t1 in
            let uu____2136 = resugar_term t2 in
            (uu____2134, uu____2135, uu____2136) in
          FStar_Parser_AST.If uu____2130 in
        mk1 uu____2129
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2176 =
          match uu____2176 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____2195 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____2195 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2198 =
          let uu____2199 =
            let uu____2207 = resugar_term e in
            let uu____2208 = FStar_List.map resugar_branch branches in
            (uu____2207, uu____2208) in
          FStar_Parser_AST.Match uu____2199 in
        mk1 uu____2198
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2230) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2283 =
          let uu____2284 =
            let uu____2289 = resugar_term e in (uu____2289, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2284 in
        mk1 uu____2283
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2307 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2307 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2323 =
                 let uu____2326 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2326 in
               match uu____2323 with
               | (univs1,td) ->
                   let uu____2333 =
                     let uu____2340 =
                       let uu____2341 = FStar_Syntax_Subst.compress td in
                       uu____2341.FStar_Syntax_Syntax.n in
                     match uu____2340 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2350,(t1,uu____2352)::(d,uu____2354)::[]) ->
                         (t1, d)
                     | uu____2388 -> failwith "wrong let binding format" in
                   (match uu____2333 with
                    | (typ,def) ->
                        let uu____2409 =
                          let uu____2413 =
                            let uu____2414 = FStar_Syntax_Subst.compress def in
                            uu____2414.FStar_Syntax_Syntax.n in
                          match uu____2413 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2422) ->
                              let uu____2445 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2445 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2454 =
                                       FStar_Options.print_implicits () in
                                     if uu____2454 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2456 -> ([], def, false) in
                        (match uu____2409 with
                         | (binders,term,is_pat_app) ->
                             let uu____2471 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2482 =
                                     let uu____2483 =
                                       let uu____2484 =
                                         let uu____2488 =
                                           bv_as_unique_ident bv in
                                         (uu____2488,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____2484 in
                                     mk_pat uu____2483 in
                                   (uu____2482, term) in
                             (match uu____2471 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2505  ->
                                              match uu____2505 with
                                              | (bv,uu____2509) ->
                                                  let uu____2510 =
                                                    let uu____2511 =
                                                      let uu____2515 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2515,
                                                        FStar_Pervasives_Native.None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2511 in
                                                  mk_pat uu____2510)) in
                                    let uu____2517 =
                                      let uu____2520 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2520) in
                                    let uu____2522 =
                                      universe_to_string univs1 in
                                    (uu____2517, uu____2522)
                                  else
                                    (let uu____2526 =
                                       let uu____2529 = resugar_term term1 in
                                       (pat, uu____2529) in
                                     let uu____2530 =
                                       universe_to_string univs1 in
                                     (uu____2526, uu____2530))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____2556 =
                   let uu____2557 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____2557 in
                 Obj.magic
                   (if uu____2556
                    then FStar_Pervasives_Native.fst
                    else
                      (fun uu___189_2569  ->
                         match uu___189_2569 with
                         | ((pat,body2),univs1) ->
                             let uu____2581 =
                               mk1
                                 (FStar_Parser_AST.Labeled
                                    (body2, univs1, true)) in
                             (pat, uu____2581))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2594) ->
        let s =
          let uu____2608 =
            let uu____2609 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2609 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2608 in
        let uu____2613 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2613
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___190_2623 =
          match uu___190_2623 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2624 =
                let uu____2625 = FStar_Syntax_Subst.compress e in
                uu____2625.FStar_Syntax_Syntax.n in
              (match uu____2624 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2651 =
                       let uu____2652 = FStar_Syntax_Subst.compress h in
                       uu____2652.FStar_Syntax_Syntax.n in
                     match uu____2651 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2659 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2659, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2667 = aux h1 in
                         (match uu____2667 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2679 -> failwith "wrong Data_app head format" in
                   let uu____2683 = aux head1 in
                   (match uu____2683 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2698 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2698, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2707  ->
                               match uu____2707 with
                               | (t1,uu____2713) ->
                                   let uu____2714 = resugar_term t1 in
                                   (uu____2714, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2715 =
                          FStar_Parser_Const.is_tuple_data_lid' head2 in
                        if uu____2715
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2720 = FStar_Options.print_universes () in
                           if uu____2720
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2730,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2736,uu____2737) -> resugar_term e
                    | uu____2742 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2743 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2749,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2765 =
                      let uu____2766 =
                        let uu____2771 = resugar_seq t11 in
                        (uu____2771, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2766 in
                    mk1 uu____2765
                | uu____2773 -> t1 in
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
               | uu____2786 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____2788 =
                let uu____2789 = FStar_Syntax_Subst.compress e in
                uu____2789.FStar_Syntax_Syntax.n in
              (match uu____2788 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2793;
                      FStar_Syntax_Syntax.pos = uu____2794;
                      FStar_Syntax_Syntax.vars = uu____2795;_},(term,uu____2797)::[])
                   -> resugar_term term
               | uu____2819 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2841  ->
                       match uu____2841 with
                       | (x,uu____2845) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2847,p) ->
             let uu____2849 =
               let uu____2850 =
                 let uu____2854 = resugar_term e in (uu____2854, l, p) in
               FStar_Parser_AST.Labeled uu____2850 in
             mk1 uu____2849
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2863 =
               let uu____2864 =
                 let uu____2869 = resugar_term e in
                 let uu____2870 =
                   let uu____2871 =
                     let uu____2872 =
                       let uu____2878 =
                         let uu____2882 =
                           let uu____2885 = resugar_term t1 in
                           (uu____2885, FStar_Parser_AST.Nothing) in
                         [uu____2882] in
                       (name1, uu____2878) in
                     FStar_Parser_AST.Construct uu____2872 in
                   mk1 uu____2871 in
                 (uu____2869, uu____2870, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2864 in
             mk1 uu____2863
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2895,t1) ->
             let uu____2901 =
               let uu____2902 =
                 let uu____2907 = resugar_term e in
                 let uu____2908 =
                   let uu____2909 =
                     let uu____2910 =
                       let uu____2916 =
                         let uu____2920 =
                           let uu____2923 = resugar_term t1 in
                           (uu____2923, FStar_Parser_AST.Nothing) in
                         [uu____2920] in
                       (name1, uu____2916) in
                     FStar_Parser_AST.Construct uu____2910 in
                   mk1 uu____2909 in
                 (uu____2907, uu____2908, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2902 in
             mk1 uu____2901)
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
             let uu____2954 = FStar_Options.print_universes () in
             if uu____2954
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
             let uu____2990 = FStar_Options.print_universes () in
             if uu____2990
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
          let uu____3013 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____3013, FStar_Parser_AST.Nothing) in
        let uu____3014 = FStar_Options.print_effect_args () in
        if uu____3014
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___191_3054 =
                match uu___191_3054 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3096 -> aux l tl1
                     | uu____3101 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3121  ->
                 match uu____3121 with
                 | (e,uu____3127) ->
                     let uu____3128 = resugar_term e in
                     (uu____3128, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___192_3142 =
            match uu___192_3142 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3162 = resugar_term e in
                       (uu____3162, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3165 -> aux l tl1) in
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
      let uu____3189 = b in
      match uu____3189 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3193 =
                 let uu____3194 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3194 in
               FStar_Parser_AST.mk_binder uu____3193 r
                 FStar_Parser_AST.Type_level FStar_Pervasives_Native.None
           | uu____3195 ->
               let uu____3196 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3196
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level FStar_Pervasives_Native.None
               else
                 (let uu____3198 =
                    let uu____3199 =
                      let uu____3202 = bv_as_unique_ident x in
                      (uu____3202, e) in
                    FStar_Parser_AST.Annotated uu____3199 in
                  FStar_Parser_AST.mk_binder uu____3198 r
                    FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3210 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3210 in
      let uu____3211 =
        let uu____3212 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3212.FStar_Syntax_Syntax.n in
      match uu____3211 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3218 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____3218
          else
            (let uu____3220 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3220
               (fun aq  ->
                  let uu____3226 =
                    let uu____3227 =
                      let uu____3228 =
                        let uu____3232 = bv_as_unique_ident x in
                        (uu____3232, aq) in
                      FStar_Parser_AST.PatVar uu____3228 in
                    mk1 uu____3227 in
                  FStar_Pervasives_Native.Some uu____3226))
      | uu____3234 ->
          let uu____3235 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3235
            (fun aq  ->
               let pat =
                 let uu____3242 =
                   let uu____3243 =
                     let uu____3247 = bv_as_unique_ident x in
                     (uu____3247, aq) in
                   FStar_Parser_AST.PatVar uu____3243 in
                 mk1 uu____3242 in
               let uu____3249 = FStar_Options.print_bound_var_types () in
               if uu____3249
               then
                 let uu____3251 =
                   let uu____3252 =
                     let uu____3253 =
                       let uu____3256 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3256) in
                     FStar_Parser_AST.PatAscribed uu____3253 in
                   mk1 uu____3252 in
                 FStar_Pervasives_Native.Some uu____3251
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
              (fun uu____3302  -> match uu____3302 with | (p2,b) -> aux p2)
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
              (fun uu____3331  -> match uu____3331 with | (p2,b) -> aux p2)
              args in
          let uu____3336 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3336
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3344;
             FStar_Syntax_Syntax.fv_delta = uu____3345;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3366 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3366 FStar_List.rev in
          let args1 =
            let uu____3375 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3385  ->
                      match uu____3385 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3375 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3427 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3427
            | (hd1::tl1,hd2::tl2) ->
                let uu____3441 = map21 tl1 tl2 in (hd1, hd2) :: uu____3441 in
          let args2 =
            let uu____3451 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3451 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3479  -> match uu____3479 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3490 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3490 with
           | FStar_Pervasives_Native.Some (op,uu____3495) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____3500 =
                 let uu____3501 =
                   let uu____3505 = bv_as_unique_ident v1 in
                   (uu____3505, FStar_Pervasives_Native.None) in
                 FStar_Parser_AST.PatVar uu____3501 in
               mk1 uu____3500)
      | FStar_Syntax_Syntax.Pat_wild uu____3507 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3515 =
              let uu____3516 =
                let uu____3520 = bv_as_unique_ident bv in
                (uu____3520, FStar_Pervasives_Native.None) in
              FStar_Parser_AST.PatVar uu____3516 in
            mk1 uu____3515 in
          let uu____3522 = FStar_Options.print_bound_var_types () in
          if uu____3522
          then
            let uu____3523 =
              let uu____3524 =
                let uu____3527 = resugar_term term in (pat, uu____3527) in
              FStar_Parser_AST.PatAscribed uu____3524 in
            mk1 uu____3523
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___193_3532  ->
    match uu___193_3532 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3538 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3539 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____3540 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____3543 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____3548 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____3553 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___194_3556  ->
    match uu___194_3556 with
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
          (tylid,uvs,bs,t,uu____3578,datacons) ->
          let uu____3584 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3595,uu____3596,uu____3597,inductive_lid,uu____3599,uu____3600)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3603 -> failwith "unexpected")) in
          (match uu____3584 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3614 = FStar_Options.print_implicits () in
                 if uu____3614 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3621 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___195_3623  ->
                           match uu___195_3623 with
                           | FStar_Syntax_Syntax.RecordType uu____3624 ->
                               true
                           | uu____3629 -> false)) in
                 if uu____3621
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3657,univs1,term,uu____3660,num,uu____3662)
                         ->
                         let uu____3665 =
                           let uu____3666 = FStar_Syntax_Subst.compress term in
                           uu____3666.FStar_Syntax_Syntax.n in
                         (match uu____3665 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3675) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3706  ->
                                        match uu____3706 with
                                        | (b,qual) ->
                                            let uu____3715 =
                                              let uu____3716 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3716 in
                                            let uu____3717 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3715, uu____3717,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____3723 -> failwith "unexpected")
                     | uu____3729 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____3796,num,uu____3798) ->
                          let c =
                            let uu____3808 =
                              let uu____3810 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____3810 in
                            ((l.FStar_Ident.ident), uu____3808,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____3819 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____3858 ->
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
        let uu____3872 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____3872;
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
      let uu____3885 = ts in
      match uu____3885 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3891 =
            let uu____3892 =
              let uu____3899 =
                let uu____3904 =
                  let uu____3908 =
                    let uu____3909 =
                      let uu____3916 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____3916) in
                    FStar_Parser_AST.TyconAbbrev uu____3909 in
                  (uu____3908, FStar_Pervasives_Native.None) in
                [uu____3904] in
              (false, uu____3899) in
            FStar_Parser_AST.Tycon uu____3892 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3891
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
            let uu____3955 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3955 with
            | (bs,action_defn) ->
                let uu____3960 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3960 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3966 = FStar_Options.print_implicits () in
                       if uu____3966
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3970 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3970 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3979 =
                           let uu____3985 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3985,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3979 in
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
          let uu____4024 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4024 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4030 = FStar_Options.print_implicits () in
                if uu____4030 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4034 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4034 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4075) ->
        let uu____4080 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4091 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4100 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4104 -> false
                  | uu____4112 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4080 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4132 se1 =
               match uu____4132 with
               | (datacon_ses1,tycons) ->
                   let uu____4147 = resugar_typ datacon_ses1 se1 in
                   (match uu____4147 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4156 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4156 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4175 =
                         let uu____4176 =
                           let uu____4177 =
                             let uu____4184 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____4184) in
                           FStar_Parser_AST.Tycon uu____4177 in
                         decl'_to_decl se uu____4176 in
                       FStar_Pervasives_Native.Some uu____4175
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4201,uu____4202,uu____4203,uu____4204,uu____4205)
                            ->
                            let uu____4208 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____4208
                        | uu____4210 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4212 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4216,attrs) ->
        let uu____4222 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_4224  ->
                  match uu___196_4224 with
                  | FStar_Syntax_Syntax.Projector (uu____4225,uu____4226) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4227 -> true
                  | uu____4228 -> false)) in
        if uu____4222
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4253) ->
               let uu____4260 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____4260
           | uu____4264 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4268 =
          let uu____4269 =
            let uu____4270 =
              let uu____4273 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4273) in
            FStar_Parser_AST.Assume uu____4270 in
          decl'_to_decl se uu____4269 in
        FStar_Pervasives_Native.Some uu____4268
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4275 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4275
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4277 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4277
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____4284,t) ->
              let uu____4291 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4291
          | uu____4292 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____4297,t) ->
              let uu____4304 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4304
          | uu____4305 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____4320 -> failwith "Should not happen hopefully" in
        let uu____4325 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____4325
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4333 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4333 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4340 = FStar_Options.print_implicits () in
               if uu____4340 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4346 =
               let uu____4347 =
                 let uu____4348 =
                   let uu____4355 =
                     let uu____4360 =
                       let uu____4364 =
                         let uu____4365 =
                           let uu____4372 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____4372) in
                         FStar_Parser_AST.TyconAbbrev uu____4365 in
                       (uu____4364, FStar_Pervasives_Native.None) in
                     [uu____4360] in
                   (false, uu____4355) in
                 FStar_Parser_AST.Tycon uu____4348 in
               decl'_to_decl se uu____4347 in
             FStar_Pervasives_Native.Some uu____4346)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4387 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____4387
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4391 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___197_4393  ->
                  match uu___197_4393 with
                  | FStar_Syntax_Syntax.Projector (uu____4394,uu____4395) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4396 -> true
                  | uu____4397 -> false)) in
        if uu____4391
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____4401 =
               (let uu____4402 = FStar_Options.print_universes () in
                Prims.op_Negation uu____4402) || (FStar_List.isEmpty uvs) in
             if uu____4401
             then resugar_term t
             else
               (let uu____4404 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____4404 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____4410 =
                      let uu____4411 =
                        let uu____4415 = resugar_term t1 in
                        (uu____4415, universes, true) in
                      FStar_Parser_AST.Labeled uu____4411 in
                    FStar_Parser_AST.mk_term uu____4410
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____4416 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____4416)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4417 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____4426 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____4434 -> FStar_Pervasives_Native.None