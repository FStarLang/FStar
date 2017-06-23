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
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____94 = FStar_Options.print_universes () in
    if uu____94
    then
      let uu____95 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____95 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____121 ->
          let uu____122 = universe_to_int (Prims.parse_int "0") u in
          (match uu____122 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____127 =
                      let uu____128 =
                        let uu____129 =
                          let uu____135 = FStar_Util.string_of_int n1 in
                          (uu____135, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____129 in
                      FStar_Parser_AST.Const uu____128 in
                    mk1 uu____127 r
                | uu____141 ->
                    let e1 =
                      let uu____143 =
                        let uu____144 =
                          let uu____145 =
                            let uu____151 = FStar_Util.string_of_int n1 in
                            (uu____151, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____145 in
                        FStar_Parser_AST.Const uu____144 in
                      mk1 uu____143 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____161 ->
               let t =
                 let uu____164 =
                   let uu____165 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____165 in
                 mk1 uu____164 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____171 =
                        let uu____172 =
                          let uu____176 = resugar_universe x r in
                          (acc, uu____176, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____172 in
                      mk1 uu____171 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____178 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____185 =
              let uu____188 =
                let uu____189 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____189 in
              (uu____188, r) in
            FStar_Ident.mk_ident uu____185 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___188_203 =
      match uu___188_203 with
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
      | uu____241 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____255 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____261 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____261 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____270 ->
               let op =
                 let uu____273 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____294) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____273 in
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
      let uu____393 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____393 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____419 ->
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
                (let uu____456 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____456
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____465 =
      let uu____466 = FStar_Syntax_Subst.compress t in
      uu____466.FStar_Syntax_Syntax.n in
    match uu____465 with
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
        let uu____488 = string_to_op s in
        (match uu____488 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____502 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____512 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____519 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____524 -> true
    | uu____525 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____553 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____553 in
    let var a r =
      let uu____561 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____561 in
    let uu____562 =
      let uu____563 = FStar_Syntax_Subst.compress t in
      uu____563.FStar_Syntax_Syntax.n in
    match uu____562 with
    | FStar_Syntax_Syntax.Tm_delayed uu____566 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____583 = let uu____585 = bv_as_unique_ident x in [uu____585] in
          FStar_Ident.lid_of_ids uu____583 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____588 = let uu____590 = bv_as_unique_ident x in [uu____590] in
          FStar_Ident.lid_of_ids uu____588 in
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
          let uu____614 =
            let uu____615 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____615 in
          mk1 uu____614
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
             | uu____628 -> failwith "wrong projector format")
          else
            (let uu____631 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____634 =
                    let uu____635 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____635 in
                  let uu____636 = FStar_String.get s (Prims.parse_int "0") in
                  uu____634 <> uu____636) in
             if uu____631
             then
               let uu____637 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____637
             else
               (let uu____639 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____639))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____646 = FStar_Options.print_universes () in
        if uu____646
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____653 =
                   let uu____654 =
                     let uu____658 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____658, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____654 in
                 mk1 uu____653) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____661 = FStar_Syntax_Syntax.is_teff t in
        if uu____661
        then
          let uu____662 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____662
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____665 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____665
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____666 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____666
         | uu____667 ->
             let uu____668 = FStar_Options.print_universes () in
             if uu____668
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____679 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____679))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____682) ->
        let uu____695 = FStar_Syntax_Subst.open_term xs body in
        (match uu____695 with
         | (xs1,body1) ->
             let xs2 =
               let uu____701 = FStar_Options.print_implicits () in
               if uu____701 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____711  ->
                       match uu____711 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____731 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____731 with
         | (xs1,body1) ->
             let xs2 =
               let uu____737 = FStar_Options.print_implicits () in
               if uu____737 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____742 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____742 FStar_List.rev in
             let rec aux body3 uu___189_756 =
               match uu___189_756 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____769 =
          let uu____772 =
            let uu____773 = FStar_Syntax_Syntax.mk_binder x in [uu____773] in
          FStar_Syntax_Subst.open_term uu____772 phi in
        (match uu____769 with
         | (x1,phi1) ->
             let b =
               let uu____777 = FStar_List.hd x1 in
               resugar_binder uu____777 t.FStar_Syntax_Syntax.pos in
             let uu____780 =
               let uu____781 =
                 let uu____784 = resugar_term phi1 in (b, uu____784) in
               FStar_Parser_AST.Refine uu____781 in
             mk1 uu____780)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___190_814 =
          match uu___190_814 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____861 -> failwith "last of an empty list" in
        let rec last_two uu___191_885 =
          match uu___191_885 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____905::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____957::t1 -> last_two t1 in
        let rec last_three uu___192_985 =
          match uu___192_985 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1005::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1023::uu____1024::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1097::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1136  ->
                    match uu____1136 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1152 = FStar_Options.print_implicits () in
          if uu____1152 then args else filter_imp args in
        let uu____1161 = resugar_term_as_op e in
        (match uu____1161 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1167) ->
             (match args1 with
              | (fst1,uu____1171)::(snd1,uu____1173)::rest ->
                  let e1 =
                    let uu____1197 =
                      let uu____1198 =
                        let uu____1202 =
                          let uu____1204 = resugar_term fst1 in
                          let uu____1205 =
                            let uu____1207 = resugar_term snd1 in
                            [uu____1207] in
                          uu____1204 :: uu____1205 in
                        ((FStar_Ident.id_of_text "*"), uu____1202) in
                      FStar_Parser_AST.Op uu____1198 in
                    mk1 uu____1197 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1217  ->
                         match uu____1217 with
                         | (x,uu____1221) ->
                             let uu____1222 =
                               let uu____1223 =
                                 let uu____1227 =
                                   let uu____1229 =
                                     let uu____1231 = resugar_term x in
                                     [uu____1231] in
                                   e1 :: uu____1229 in
                                 ((FStar_Ident.id_of_text "*"), uu____1227) in
                               FStar_Parser_AST.Op uu____1223 in
                             mk1 uu____1222) e1 rest
              | uu____1233 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1239) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1264)::[] -> b
               | uu____1277 -> failwith "wrong arguments to dtuple" in
             let uu____1285 =
               let uu____1286 = FStar_Syntax_Subst.compress body in
               uu____1286.FStar_Syntax_Syntax.n in
             (match uu____1285 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1291) ->
                  let uu____1304 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1304 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1310 = FStar_Options.print_implicits () in
                         if uu____1310 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1319 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1333  ->
                            match uu____1333 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1343) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____1347) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____1350 = FStar_List.hd args1 in
             (match uu____1350 with
              | (t1,uu____1360) ->
                  let uu____1365 =
                    let uu____1366 = FStar_Syntax_Subst.compress t1 in
                    uu____1366.FStar_Syntax_Syntax.n in
                  (match uu____1365 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1371 =
                         let uu____1372 =
                           let uu____1375 = resugar_term t1 in
                           (uu____1375, f) in
                         FStar_Parser_AST.Project uu____1372 in
                       mk1 uu____1371
                   | uu____1376 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____1377) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1396 =
               match new_args with
               | (a1,uu____1410)::(a2,uu____1412)::[] -> (a1, a2)
               | uu____1437 -> failwith "wrong arguments to try_with" in
             (match uu____1396 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1463 =
                      let uu____1464 = FStar_Syntax_Subst.compress term in
                      uu____1464.FStar_Syntax_Syntax.n in
                    match uu____1463 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1469) ->
                        let uu____1482 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1482 with | (x1,e2) -> e2)
                    | uu____1487 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1489 = decomp body in resugar_term uu____1489 in
                  let handler1 =
                    let uu____1491 = decomp handler in
                    resugar_term uu____1491 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1497,uu____1498,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1515,uu____1516,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1529 =
                          let uu____1530 =
                            let uu____1535 = resugar_body t11 in
                            (uu____1535, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1530 in
                        mk1 uu____1529
                    | uu____1537 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1570 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____1586) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____1590) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1641 -> (xs, pat, t1) in
             let resugar body =
               let uu____1649 =
                 let uu____1650 = FStar_Syntax_Subst.compress body in
                 uu____1650.FStar_Syntax_Syntax.n in
               match uu____1649 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1655) ->
                   let uu____1668 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1668 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1674 = FStar_Options.print_implicits () in
                          if uu____1674 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1681 =
                          let uu____1686 =
                            let uu____1687 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1687.FStar_Syntax_Syntax.n in
                          match uu____1686 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1731  ->
                                                 match uu____1731 with
                                                 | (e2,uu____1735) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1738) ->
                                    let uu____1739 =
                                      let uu____1741 =
                                        let uu____1742 = name s r in
                                        mk1 uu____1742 in
                                      [uu____1741] in
                                    [uu____1739]
                                | uu____1745 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1750 ->
                              let uu____1751 = resugar_term body2 in
                              ([], uu____1751) in
                        (match uu____1681 with
                         | (pats,body3) ->
                             let uu____1761 = uncurry xs3 pats body3 in
                             (match uu____1761 with
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
               | uu____1788 ->
                   if op = "forall"
                   then
                     let uu____1789 =
                       let uu____1790 =
                         let uu____1797 = resugar_term body in
                         ([], [[]], uu____1797) in
                       FStar_Parser_AST.QForall uu____1790 in
                     mk1 uu____1789
                   else
                     (let uu____1804 =
                        let uu____1805 =
                          let uu____1812 = resugar_term body in
                          ([], [[]], uu____1812) in
                        FStar_Parser_AST.QExists uu____1805 in
                      mk1 uu____1804) in
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
                    (fun uu____1898  ->
                       match uu____1898 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____1903 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1903 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1914 =
                         let uu____1915 =
                           let uu____1919 =
                             let uu____1921 = last1 args1 in
                             resugar uu____1921 in
                           (op1, uu____1919) in
                         FStar_Parser_AST.Op uu____1915 in
                       mk1 uu____1914
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1936 =
                         let uu____1937 =
                           let uu____1941 =
                             let uu____1943 = last_two args1 in
                             resugar uu____1943 in
                           (op1, uu____1941) in
                         FStar_Parser_AST.Op uu____1937 in
                       mk1 uu____1936
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1958 =
                         let uu____1959 =
                           let uu____1963 =
                             let uu____1965 = last_three args1 in
                             resugar uu____1965 in
                           (op1, uu____1963) in
                         FStar_Parser_AST.Op uu____1959 in
                       mk1 uu____1958
                   | uu____1970 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1981 =
                    let uu____1982 =
                      let uu____1986 =
                        let uu____1988 = last_two args1 in resugar uu____1988 in
                      (op1, uu____1986) in
                    FStar_Parser_AST.Op uu____1982 in
                  mk1 uu____1981
              | uu____1993 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1996,t1)::[]) ->
        let bnds =
          let uu____2046 =
            let uu____2049 = resugar_pat pat in
            let uu____2050 = resugar_term e in (uu____2049, uu____2050) in
          [uu____2046] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2061,t1)::(pat2,uu____2064,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2131 =
          let uu____2132 =
            let uu____2136 = resugar_term e in
            let uu____2137 = resugar_term t1 in
            let uu____2138 = resugar_term t2 in
            (uu____2136, uu____2137, uu____2138) in
          FStar_Parser_AST.If uu____2132 in
        mk1 uu____2131
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
                              let uu____2435 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2435 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2444 =
                                       FStar_Options.print_implicits () in
                                     if uu____2444 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2446 -> ([], def, false) in
                        (match uu____2409 with
                         | (binders,term,is_pat_app) ->
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
             let bnds2 =
               let f =
                 let uu____2546 =
                   let uu____2547 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____2547 in
                 Obj.magic
                   (if uu____2546
                    then FStar_Pervasives_Native.fst
                    else
                      (fun uu___193_2559  ->
                         match uu___193_2559 with
                         | ((pat,body2),univs1) ->
                             let uu____2571 =
                               mk1
                                 (FStar_Parser_AST.Labeled
                                    (body2, univs1, true)) in
                             (pat, uu____2571))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2584) ->
        let s =
          let uu____2602 =
            let uu____2603 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2603 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2602 in
        let uu____2604 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2604
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___194_2614 =
          match uu___194_2614 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2615 =
                let uu____2616 = FStar_Syntax_Subst.compress e in
                uu____2616.FStar_Syntax_Syntax.n in
              (match uu____2615 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2642 =
                       let uu____2643 = FStar_Syntax_Subst.compress h in
                       uu____2643.FStar_Syntax_Syntax.n in
                     match uu____2642 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2650 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2650, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2658 = aux h1 in
                         (match uu____2658 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2670 -> failwith "wrong Data_app head format" in
                   let uu____2674 = aux head1 in
                   (match uu____2674 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2691 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2691, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2704  ->
                               match uu____2704 with
                               | (t1,uu____2710) ->
                                   let uu____2711 = resugar_term t1 in
                                   (uu____2711, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2712 =
                          FStar_Parser_Const.is_tuple_data_lid' head2 in
                        if uu____2712
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2717 = FStar_Options.print_universes () in
                           if uu____2717
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2727,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2733,uu____2734) -> resugar_term e
                    | uu____2739 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2740 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2746,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2762 =
                      let uu____2763 =
                        let uu____2768 = resugar_seq t11 in
                        (uu____2768, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2763 in
                    mk1 uu____2762
                | uu____2770 -> t1 in
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
               | uu____2783 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____2785 =
                let uu____2786 = FStar_Syntax_Subst.compress e in
                uu____2786.FStar_Syntax_Syntax.n in
              (match uu____2785 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2790;
                      FStar_Syntax_Syntax.pos = uu____2791;
                      FStar_Syntax_Syntax.vars = uu____2792;_},(term,uu____2794)::[])
                   -> resugar_term term
               | uu____2816 -> failwith "mutable_rval should have app term") in
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
         | FStar_Syntax_Syntax.Meta_alien (uu____2856,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2865 =
               let uu____2866 =
                 let uu____2871 = resugar_term e in
                 let uu____2872 =
                   let uu____2873 =
                     let uu____2874 =
                       let uu____2880 =
                         let uu____2884 =
                           let uu____2887 = resugar_term t1 in
                           (uu____2887, FStar_Parser_AST.Nothing) in
                         [uu____2884] in
                       (name1, uu____2880) in
                     FStar_Parser_AST.Construct uu____2874 in
                   mk1 uu____2873 in
                 (uu____2871, uu____2872, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2866 in
             mk1 uu____2865
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2897,t1) ->
             let uu____2903 =
               let uu____2904 =
                 let uu____2909 = resugar_term e in
                 let uu____2910 =
                   let uu____2911 =
                     let uu____2912 =
                       let uu____2918 =
                         let uu____2922 =
                           let uu____2925 = resugar_term t1 in
                           (uu____2925, FStar_Parser_AST.Nothing) in
                         [uu____2922] in
                       (name1, uu____2918) in
                     FStar_Parser_AST.Construct uu____2912 in
                   mk1 uu____2911 in
                 (uu____2909, uu____2910, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2904 in
             mk1 uu____2903)
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
             let uu____2956 = FStar_Options.print_universes () in
             if uu____2956
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
             let uu____2992 = FStar_Options.print_universes () in
             if uu____2992
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
          let uu____3015 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____3015, FStar_Parser_AST.Nothing) in
        let uu____3016 = FStar_Options.print_effect_args () in
        if uu____3016
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___195_3057 =
                match uu___195_3057 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3099 -> aux l tl1
                     | uu____3104 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3128  ->
                 match uu____3128 with
                 | (e,uu____3134) ->
                     let uu____3135 = resugar_term e in
                     (uu____3135, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___196_3149 =
            match uu___196_3149 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3169 = resugar_term e in
                       (uu____3169, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3172 -> aux l tl1) in
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
      let uu____3196 = b in
      match uu____3196 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3200 =
                 let uu____3201 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3201 in
               FStar_Parser_AST.mk_binder uu____3200 r
                 FStar_Parser_AST.Type_level FStar_Pervasives_Native.None
           | uu____3202 ->
               let uu____3203 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3203
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level FStar_Pervasives_Native.None
               else
                 (let uu____3205 =
                    let uu____3206 =
                      let uu____3209 = bv_as_unique_ident x in
                      (uu____3209, e) in
                    FStar_Parser_AST.Annotated uu____3206 in
                  FStar_Parser_AST.mk_binder uu____3205 r
                    FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3217 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3217 in
      let uu____3218 =
        let uu____3219 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3219.FStar_Syntax_Syntax.n in
      match uu____3218 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3225 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____3225
          else
            (let uu____3227 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3227
               (fun aq  ->
                  let uu____3235 =
                    let uu____3236 =
                      let uu____3237 =
                        let uu____3241 = bv_as_unique_ident x in
                        (uu____3241, aq) in
                      FStar_Parser_AST.PatVar uu____3237 in
                    mk1 uu____3236 in
                  FStar_Pervasives_Native.Some uu____3235))
      | uu____3243 ->
          let uu____3244 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3244
            (fun aq  ->
               let pat =
                 let uu____3255 =
                   let uu____3256 =
                     let uu____3260 = bv_as_unique_ident x in
                     (uu____3260, aq) in
                   FStar_Parser_AST.PatVar uu____3256 in
                 mk1 uu____3255 in
               let uu____3262 = FStar_Options.print_bound_var_types () in
               if uu____3262
               then
                 let uu____3264 =
                   let uu____3265 =
                     let uu____3266 =
                       let uu____3269 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3269) in
                     FStar_Parser_AST.PatAscribed uu____3266 in
                   mk1 uu____3265 in
                 FStar_Pervasives_Native.Some uu____3264
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
              (fun uu____3306  -> match uu____3306 with | (p2,b) -> aux p2)
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
              (fun uu____3328  -> match uu____3328 with | (p2,b) -> aux p2)
              args in
          let uu____3333 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3333
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3337;
             FStar_Syntax_Syntax.fv_delta = uu____3338;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3354 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3354 FStar_List.rev in
          let args1 =
            let uu____3364 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3376  ->
                      match uu____3376 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3364 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3418 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3418
            | (hd1::tl1,hd2::tl2) ->
                let uu____3432 = map21 tl1 tl2 in (hd1, hd2) :: uu____3432 in
          let args2 =
            let uu____3442 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3442 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3471  -> match uu____3471 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3478 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3478 with
           | FStar_Pervasives_Native.Some (op,uu____3483) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____3488 =
                 let uu____3489 =
                   let uu____3493 = bv_as_unique_ident v1 in
                   (uu____3493, FStar_Pervasives_Native.None) in
                 FStar_Parser_AST.PatVar uu____3489 in
               mk1 uu____3488)
      | FStar_Syntax_Syntax.Pat_wild uu____3495 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3503 =
              let uu____3504 =
                let uu____3508 = bv_as_unique_ident bv in
                (uu____3508, FStar_Pervasives_Native.None) in
              FStar_Parser_AST.PatVar uu____3504 in
            mk1 uu____3503 in
          let uu____3510 = FStar_Options.print_bound_var_types () in
          if uu____3510
          then
            let uu____3511 =
              let uu____3512 =
                let uu____3515 = resugar_term term in (pat, uu____3515) in
              FStar_Parser_AST.PatAscribed uu____3512 in
            mk1 uu____3511
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___197_3521  ->
    match uu___197_3521 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3527 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3528 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____3529 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____3532 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____3537 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____3542 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___198_3546  ->
    match uu___198_3546 with
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
          (tylid,uvs,bs,t,uu____3568,datacons) ->
          let uu____3574 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3592,uu____3593,uu____3594,inductive_lid,uu____3596,uu____3597)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3600 -> failwith "unexpected")) in
          (match uu____3574 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3612 = FStar_Options.print_implicits () in
                 if uu____3612 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3620 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___199_3624  ->
                           match uu___199_3624 with
                           | FStar_Syntax_Syntax.RecordType uu____3625 ->
                               true
                           | uu____3630 -> false)) in
                 if uu____3620
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3658,univs1,term,uu____3661,num,uu____3663)
                         ->
                         let uu____3666 =
                           let uu____3667 = FStar_Syntax_Subst.compress term in
                           uu____3667.FStar_Syntax_Syntax.n in
                         (match uu____3666 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3676) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3712  ->
                                        match uu____3712 with
                                        | (b,qual) ->
                                            let uu____3721 =
                                              let uu____3722 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3722 in
                                            let uu____3723 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3721, uu____3723,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____3729 -> failwith "unexpected")
                     | uu____3735 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____3802,num,uu____3804) ->
                          let c =
                            let uu____3814 =
                              let uu____3816 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____3816 in
                            ((l.FStar_Ident.ident), uu____3814,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____3825 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____3864 ->
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
        let uu____3881 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____3881;
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
      let uu____3898 = ts in
      match uu____3898 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3904 =
            let uu____3905 =
              let uu____3912 =
                let uu____3917 =
                  let uu____3921 =
                    let uu____3922 =
                      let uu____3929 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____3929) in
                    FStar_Parser_AST.TyconAbbrev uu____3922 in
                  (uu____3921, FStar_Pervasives_Native.None) in
                [uu____3917] in
              (false, uu____3912) in
            FStar_Parser_AST.Tycon uu____3905 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3904
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
            let uu____3973 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3973 with
            | (bs,action_defn) ->
                let uu____3978 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3978 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3984 = FStar_Options.print_implicits () in
                       if uu____3984
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3988 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3988 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3998 =
                           let uu____4004 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____4004,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3998 in
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
          let uu____4043 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4043 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4049 = FStar_Options.print_implicits () in
                if uu____4049 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4053 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4053 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4096) ->
        let uu____4101 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4114 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4123 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4127 -> false
                  | uu____4135 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4101 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4155 se1 =
               match uu____4155 with
               | (datacon_ses1,tycons) ->
                   let uu____4170 = resugar_typ datacon_ses1 se1 in
                   (match uu____4170 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4179 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4179 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4198 =
                         let uu____4199 =
                           let uu____4200 =
                             let uu____4207 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____4207) in
                           FStar_Parser_AST.Tycon uu____4200 in
                         decl'_to_decl se uu____4199 in
                       FStar_Pervasives_Native.Some uu____4198
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4225,uu____4226,uu____4227,uu____4228,uu____4229)
                            ->
                            let uu____4232 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____4232
                        | uu____4234 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4236 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4240,attrs) ->
        let uu____4246 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___200_4251  ->
                  match uu___200_4251 with
                  | FStar_Syntax_Syntax.Projector (uu____4252,uu____4253) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4254 -> true
                  | uu____4255 -> false)) in
        if uu____4246
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4280) ->
               let uu____4287 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____4287
           | uu____4291 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4294,fml) ->
        let uu____4296 =
          let uu____4297 =
            let uu____4298 =
              let uu____4301 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4301) in
            FStar_Parser_AST.Assume uu____4298 in
          decl'_to_decl se uu____4297 in
        FStar_Pervasives_Native.Some uu____4296
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4303 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4303
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4305 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4305
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____4312,t) ->
              let uu____4319 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4319
          | uu____4320 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____4325,t) ->
              let uu____4332 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4332
          | uu____4333 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____4348 -> failwith "Should not happen hopefully" in
        let uu____4353 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____4353
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4361 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4361 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4368 = FStar_Options.print_implicits () in
               if uu____4368 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4375 =
               let uu____4376 =
                 let uu____4377 =
                   let uu____4384 =
                     let uu____4389 =
                       let uu____4393 =
                         let uu____4394 =
                           let uu____4401 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____4401) in
                         FStar_Parser_AST.TyconAbbrev uu____4394 in
                       (uu____4393, FStar_Pervasives_Native.None) in
                     [uu____4389] in
                   (false, uu____4384) in
                 FStar_Parser_AST.Tycon uu____4377 in
               decl'_to_decl se uu____4376 in
             FStar_Pervasives_Native.Some uu____4375)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4416 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____4416
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4420 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___201_4425  ->
                  match uu___201_4425 with
                  | FStar_Syntax_Syntax.Projector (uu____4426,uu____4427) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4428 -> true
                  | uu____4429 -> false)) in
        if uu____4420
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____4433 =
               (let uu____4436 = FStar_Options.print_universes () in
                Prims.op_Negation uu____4436) || (FStar_List.isEmpty uvs) in
             if uu____4433
             then resugar_term t
             else
               (let uu____4438 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____4438 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____4444 =
                      let uu____4445 =
                        let uu____4449 = resugar_term t1 in
                        (uu____4449, universes, true) in
                      FStar_Parser_AST.Labeled uu____4445 in
                    FStar_Parser_AST.mk_term uu____4444
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____4450 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____4450)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4451 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____4460 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____4468 -> FStar_Pervasives_Native.None