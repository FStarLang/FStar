open Prims
let doc_to_string: FStar_Pprint.document -> Prims.string =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
let parser_term_to_string: FStar_Parser_AST.term -> Prims.string =
  fun t  ->
    let uu____9 = FStar_Parser_ToDocument.term_to_document t in
    doc_to_string uu____9
let map_opt f l =
  let uu____38 =
    FStar_Util.choose_map
      (fun uu____45  -> fun x  -> let uu____47 = f x in ((), uu____47)) () l in
  FStar_Pervasives_Native.snd uu____38
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____56 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____56
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___187_93  ->
          match uu___187_93 with
          | (uu____97,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____98)) -> false
          | uu____100 -> true))
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
let resugar_imp:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.imp
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        FStar_Parser_AST.Hash
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        failwith "Not an imp"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        failwith "Not an imp"
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
      | uu____143 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____150 = FStar_Options.print_universes () in
    if uu____150
    then
      let uu____151 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____151 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____177 ->
          let uu____178 = universe_to_int (Prims.parse_int "0") u in
          (match uu____178 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____183 =
                      let uu____184 =
                        let uu____185 =
                          let uu____191 = FStar_Util.string_of_int n1 in
                          (uu____191, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____185 in
                      FStar_Parser_AST.Const uu____184 in
                    mk1 uu____183 r
                | uu____197 ->
                    let e1 =
                      let uu____199 =
                        let uu____200 =
                          let uu____201 =
                            let uu____207 = FStar_Util.string_of_int n1 in
                            (uu____207, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____201 in
                        FStar_Parser_AST.Const uu____200 in
                      mk1 uu____199 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____217 ->
               let t =
                 let uu____220 =
                   let uu____221 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____221 in
                 mk1 uu____220 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____227 =
                        let uu____228 =
                          let uu____232 = resugar_universe x r in
                          (acc, uu____232, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____228 in
                      mk1 uu____227 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____234 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____241 =
              let uu____244 =
                let uu____245 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____245 in
              (uu____244, r) in
            FStar_Ident.mk_ident uu____241 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___188_259 =
      match uu___188_259 with
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
      | uu____297 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____311 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____317 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____317 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____326 ->
               let op =
                 let uu____329 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____350) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____329 in
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
      let uu____449 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____449 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____475 ->
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
                (let uu____512 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____512
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____521 =
      let uu____522 = FStar_Syntax_Subst.compress t in
      uu____522.FStar_Syntax_Syntax.n in
    match uu____521 with
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
        let uu____544 = string_to_op s in
        (match uu____544 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____558 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____568 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____575 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____580 -> true
    | uu____581 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____610 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____610 in
    let var a r =
      let uu____618 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____618 in
    let uu____619 =
      let uu____620 = FStar_Syntax_Subst.compress t in
      uu____620.FStar_Syntax_Syntax.n in
    match uu____619 with
    | FStar_Syntax_Syntax.Tm_delayed uu____623 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____640 = let uu____642 = bv_as_unique_ident x in [uu____642] in
          FStar_Ident.lid_of_ids uu____640 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____645 = let uu____647 = bv_as_unique_ident x in [uu____647] in
          FStar_Ident.lid_of_ids uu____645 in
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
          let uu____671 =
            let uu____672 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____672 in
          mk1 uu____671
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
             | uu____685 -> failwith "wrong projector format")
          else
            (let uu____688 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____691 =
                    let uu____692 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____692 in
                  let uu____693 = FStar_String.get s (Prims.parse_int "0") in
                  uu____691 <> uu____693) in
             if uu____688
             then
               let uu____694 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____694
             else
               (let uu____696 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____696))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____703 = FStar_Options.print_universes () in
        if uu____703
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____710 =
                   let uu____711 =
                     let uu____715 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____715, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____711 in
                 mk1 uu____710) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____718 = FStar_Syntax_Syntax.is_teff t in
        if uu____718
        then
          let uu____719 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____719
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____722 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____722
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____723 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____723
         | uu____724 ->
             let uu____725 = FStar_Options.print_universes () in
             if uu____725
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____736 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____736))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____739) ->
        let uu____752 = FStar_Syntax_Subst.open_term xs body in
        (match uu____752 with
         | (xs1,body1) ->
             let xs2 =
               let uu____758 = FStar_Options.print_implicits () in
               if uu____758 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____768  ->
                       match uu____768 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____788 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____788 with
         | (xs1,body1) ->
             let xs2 =
               let uu____794 = FStar_Options.print_implicits () in
               if uu____794 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____799 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____799 FStar_List.rev in
             let rec aux body3 uu___189_813 =
               match uu___189_813 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____826 =
          let uu____829 =
            let uu____830 = FStar_Syntax_Syntax.mk_binder x in [uu____830] in
          FStar_Syntax_Subst.open_term uu____829 phi in
        (match uu____826 with
         | (x1,phi1) ->
             let b =
               let uu____834 =
                 let uu____836 = FStar_List.hd x1 in
                 resugar_binder uu____836 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____834 in
             let uu____839 =
               let uu____840 =
                 let uu____843 = resugar_term phi1 in (b, uu____843) in
               FStar_Parser_AST.Refine uu____840 in
             mk1 uu____839)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___190_873 =
          match uu___190_873 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____920 -> failwith "last of an empty list" in
        let rec last_two uu___191_944 =
          match uu___191_944 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____964::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1016::t1 -> last_two t1 in
        let rec last_three uu___192_1044 =
          match uu___192_1044 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1064::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1082::uu____1083::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1156::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1209  ->
                    match uu____1209 with
                    | (e2,qual) ->
                        let uu____1220 = resugar_term e2 in
                        (uu____1220, qual))) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1232  ->
                 match uu____1232 with
                 | (x,qual) ->
                     let uu____1240 =
                       let uu____1241 =
                         let uu____1245 = resugar_imp qual in
                         (acc, x, uu____1245) in
                       FStar_Parser_AST.App uu____1241 in
                     mk1 uu____1240) e2 args2 in
        let args1 =
          let uu____1252 = FStar_Options.print_implicits () in
          if uu____1252 then args else filter_imp args in
        let uu____1261 = resugar_term_as_op e in
        (match uu____1261 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1267) ->
             (match args1 with
              | (fst1,uu____1271)::(snd1,uu____1273)::rest ->
                  let e1 =
                    let uu____1297 =
                      let uu____1298 =
                        let uu____1302 =
                          let uu____1304 = resugar_term fst1 in
                          let uu____1305 =
                            let uu____1307 = resugar_term snd1 in
                            [uu____1307] in
                          uu____1304 :: uu____1305 in
                        ((FStar_Ident.id_of_text "*"), uu____1302) in
                      FStar_Parser_AST.Op uu____1298 in
                    mk1 uu____1297 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1317  ->
                         match uu____1317 with
                         | (x,uu____1321) ->
                             let uu____1322 =
                               let uu____1323 =
                                 let uu____1327 =
                                   let uu____1329 =
                                     let uu____1331 = resugar_term x in
                                     [uu____1331] in
                                   e1 :: uu____1329 in
                                 ((FStar_Ident.id_of_text "*"), uu____1327) in
                               FStar_Parser_AST.Op uu____1323 in
                             mk1 uu____1322) e1 rest
              | uu____1333 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1339) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1364)::[] -> b
               | uu____1377 -> failwith "wrong arguments to dtuple" in
             let uu____1385 =
               let uu____1386 = FStar_Syntax_Subst.compress body in
               uu____1386.FStar_Syntax_Syntax.n in
             (match uu____1385 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1391) ->
                  let uu____1404 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1404 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1410 = FStar_Options.print_implicits () in
                         if uu____1410 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1419 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1433  ->
                            match uu____1433 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1443) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____1447) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____1450 = FStar_List.hd args1 in
             (match uu____1450 with
              | (t1,uu____1460) ->
                  let uu____1465 =
                    let uu____1466 = FStar_Syntax_Subst.compress t1 in
                    uu____1466.FStar_Syntax_Syntax.n in
                  (match uu____1465 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1471 =
                         let uu____1472 =
                           let uu____1475 = resugar_term t1 in
                           (uu____1475, f) in
                         FStar_Parser_AST.Project uu____1472 in
                       mk1 uu____1471
                   | uu____1476 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____1477) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1496 =
               match new_args with
               | (a1,uu____1510)::(a2,uu____1512)::[] -> (a1, a2)
               | uu____1537 -> failwith "wrong arguments to try_with" in
             (match uu____1496 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1563 =
                      let uu____1564 = FStar_Syntax_Subst.compress term in
                      uu____1564.FStar_Syntax_Syntax.n in
                    match uu____1563 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1569) ->
                        let uu____1582 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1582 with | (x1,e2) -> e2)
                    | uu____1587 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1589 = decomp body in resugar_term uu____1589 in
                  let handler1 =
                    let uu____1591 = decomp handler in
                    resugar_term uu____1591 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1597,uu____1598,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1615,uu____1616,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1629 =
                          let uu____1630 =
                            let uu____1635 = resugar_body t11 in
                            (uu____1635, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1630 in
                        mk1 uu____1629
                    | uu____1637 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1670 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____1686) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____1690) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1741 -> (xs, pat, t1) in
             let resugar body =
               let uu____1749 =
                 let uu____1750 = FStar_Syntax_Subst.compress body in
                 uu____1750.FStar_Syntax_Syntax.n in
               match uu____1749 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1755) ->
                   let uu____1768 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1768 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1774 = FStar_Options.print_implicits () in
                          if uu____1774 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1781 =
                          let uu____1786 =
                            let uu____1787 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1787.FStar_Syntax_Syntax.n in
                          match uu____1786 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1831  ->
                                                 match uu____1831 with
                                                 | (e2,uu____1835) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1838) ->
                                    let uu____1839 =
                                      let uu____1841 =
                                        let uu____1842 = name s r in
                                        mk1 uu____1842 in
                                      [uu____1841] in
                                    [uu____1839]
                                | uu____1845 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1850 ->
                              let uu____1851 = resugar_term body2 in
                              ([], uu____1851) in
                        (match uu____1781 with
                         | (pats,body3) ->
                             let uu____1861 = uncurry xs3 pats body3 in
                             (match uu____1861 with
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
               | uu____1888 ->
                   if op = "forall"
                   then
                     let uu____1889 =
                       let uu____1890 =
                         let uu____1897 = resugar_term body in
                         ([], [[]], uu____1897) in
                       FStar_Parser_AST.QForall uu____1890 in
                     mk1 uu____1889
                   else
                     (let uu____1904 =
                        let uu____1905 =
                          let uu____1912 = resugar_term body in
                          ([], [[]], uu____1912) in
                        FStar_Parser_AST.QExists uu____1905 in
                      mk1 uu____1904) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1935)::[] -> resugar b
                | uu____1948 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____1955) ->
             let uu____1958 = FStar_List.hd args1 in
             (match uu____1958 with | (e1,uu____1968) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1998  ->
                       match uu____1998 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____2003 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2003 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2014 =
                         let uu____2015 =
                           let uu____2019 =
                             let uu____2021 = last1 args1 in
                             resugar uu____2021 in
                           (op1, uu____2019) in
                         FStar_Parser_AST.Op uu____2015 in
                       mk1 uu____2014
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2036 =
                         let uu____2037 =
                           let uu____2041 =
                             let uu____2043 = last_two args1 in
                             resugar uu____2043 in
                           (op1, uu____2041) in
                         FStar_Parser_AST.Op uu____2037 in
                       mk1 uu____2036
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2058 =
                         let uu____2059 =
                           let uu____2063 =
                             let uu____2065 = last_three args1 in
                             resugar uu____2065 in
                           (op1, uu____2063) in
                         FStar_Parser_AST.Op uu____2059 in
                       mk1 uu____2058
                   | uu____2070 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____2081 =
                    let uu____2082 =
                      let uu____2086 =
                        let uu____2088 = last_two args1 in resugar uu____2088 in
                      (op1, uu____2086) in
                    FStar_Parser_AST.Op uu____2082 in
                  mk1 uu____2081
              | uu____2093 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____2096,t1)::[]) ->
        let bnds =
          let uu____2146 =
            let uu____2149 = resugar_pat pat in
            let uu____2150 = resugar_term e in (uu____2149, uu____2150) in
          [uu____2146] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2161,t1)::(pat2,uu____2164,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2231 =
          let uu____2232 =
            let uu____2236 = resugar_term e in
            let uu____2237 = resugar_term t1 in
            let uu____2238 = resugar_term t2 in
            (uu____2236, uu____2237, uu____2238) in
          FStar_Parser_AST.If uu____2232 in
        mk1 uu____2231
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2276 =
          match uu____2276 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____2295 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____2295 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2298 =
          let uu____2299 =
            let uu____2307 = resugar_term e in
            let uu____2308 = FStar_List.map resugar_branch branches in
            (uu____2307, uu____2308) in
          FStar_Parser_AST.Match uu____2299 in
        mk1 uu____2298
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2330) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2383 =
          let uu____2384 =
            let uu____2389 = resugar_term e in (uu____2389, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2384 in
        mk1 uu____2383
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2407 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2407 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2423 =
                 let uu____2426 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2426 in
               match uu____2423 with
               | (univs1,td) ->
                   let uu____2433 =
                     let uu____2440 =
                       let uu____2441 = FStar_Syntax_Subst.compress td in
                       uu____2441.FStar_Syntax_Syntax.n in
                     match uu____2440 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2450,(t1,uu____2452)::(d,uu____2454)::[]) ->
                         (t1, d)
                     | uu____2488 -> failwith "wrong let binding format" in
                   (match uu____2433 with
                    | (typ,def) ->
                        let uu____2509 =
                          let uu____2513 =
                            let uu____2514 = FStar_Syntax_Subst.compress def in
                            uu____2514.FStar_Syntax_Syntax.n in
                          match uu____2513 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2522) ->
                              let uu____2535 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2535 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2544 =
                                       FStar_Options.print_implicits () in
                                     if uu____2544 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2546 -> ([], def, false) in
                        (match uu____2509 with
                         | (binders,term,is_pat_app) ->
                             let uu____2561 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2568 =
                                     let uu____2569 =
                                       let uu____2570 =
                                         let uu____2574 =
                                           bv_as_unique_ident bv in
                                         (uu____2574,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____2570 in
                                     mk_pat uu____2569 in
                                   (uu____2568, term) in
                             (match uu____2561 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____2596  ->
                                              match uu____2596 with
                                              | (bv,q) ->
                                                  let uu____2605 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____2605
                                                    (fun q1  ->
                                                       let uu____2613 =
                                                         let uu____2614 =
                                                           let uu____2618 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____2618, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____2614 in
                                                       mk_pat uu____2613))) in
                                    let uu____2620 =
                                      let uu____2623 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2623) in
                                    let uu____2625 =
                                      universe_to_string univs1 in
                                    (uu____2620, uu____2625)
                                  else
                                    (let uu____2629 =
                                       let uu____2632 = resugar_term term1 in
                                       (pat, uu____2632) in
                                     let uu____2633 =
                                       universe_to_string univs1 in
                                     (uu____2629, uu____2633))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____2659 =
                   let uu____2660 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____2660 in
                 Obj.magic
                   (if uu____2659
                    then FStar_Pervasives_Native.fst
                    else
                      (fun uu___193_2672  ->
                         match uu___193_2672 with
                         | ((pat,body2),univs1) ->
                             let uu____2684 =
                               if univs1 = ""
                               then body2
                               else
                                 mk1
                                   (FStar_Parser_AST.Labeled
                                      (body2, univs1, true)) in
                             (pat, uu____2684))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2698) ->
        let s =
          let uu____2716 =
            let uu____2717 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2717 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2716 in
        let uu____2718 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2718
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___194_2728 =
          match uu___194_2728 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____2742 =
                  let uu____2743 = FStar_Syntax_Subst.compress h in
                  uu____2743.FStar_Syntax_Syntax.n in
                match uu____2742 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____2756 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____2756, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____2773 = head_fv_universes_args h1 in
                    (match uu____2773 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____2829 = head_fv_universes_args head1 in
                    (match uu____2829 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____2873 ->
                    let uu____2874 =
                      let uu____2875 =
                        let uu____2876 =
                          let uu____2877 = resugar_term h in
                          parser_term_to_string uu____2877 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____2876 in
                      FStar_Errors.Err uu____2875 in
                    raise uu____2874 in
              let uu____2887 =
                try
                  let uu____2918 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____2918
                with
                | FStar_Errors.Err uu____2932 ->
                    let uu____2933 =
                      let uu____2934 =
                        let uu____2937 =
                          let uu____2938 =
                            let uu____2939 = resugar_term e in
                            parser_term_to_string uu____2939 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____2938 in
                        (uu____2937, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____2934 in
                    raise uu____2933 in
              (match uu____2887 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____2973 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____2973, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.map
                       (fun uu____2988  ->
                          match uu____2988 with
                          | (t1,q) ->
                              let uu____2998 = resugar_term t1 in
                              let uu____2999 = resugar_imp q in
                              (uu____2998, uu____2999)) args in
                   let args2 =
                     let uu____3004 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____3006 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____3006) in
                     if uu____3004
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____3021,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____3037 =
                      let uu____3038 =
                        let uu____3043 = resugar_seq t11 in
                        (uu____3043, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____3038 in
                    mk1 uu____3037
                | uu____3045 -> t1 in
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
               | uu____3058 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____3060 =
                let uu____3061 = FStar_Syntax_Subst.compress e in
                uu____3061.FStar_Syntax_Syntax.n in
              (match uu____3060 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____3065;
                      FStar_Syntax_Syntax.pos = uu____3066;
                      FStar_Syntax_Syntax.vars = uu____3067;_},(term,uu____3069)::[])
                   -> resugar_term term
               | uu____3091 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____3116  ->
                       match uu____3116 with
                       | (x,uu____3120) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____3122,p) ->
             let uu____3124 =
               let uu____3125 =
                 let uu____3129 = resugar_term e in (uu____3129, l, p) in
               FStar_Parser_AST.Labeled uu____3125 in
             mk1 uu____3124
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____3131,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____3140 =
               let uu____3141 =
                 let uu____3146 = resugar_term e in
                 let uu____3147 =
                   let uu____3148 =
                     let uu____3149 =
                       let uu____3155 =
                         let uu____3159 =
                           let uu____3162 = resugar_term t1 in
                           (uu____3162, FStar_Parser_AST.Nothing) in
                         [uu____3159] in
                       (name1, uu____3155) in
                     FStar_Parser_AST.Construct uu____3149 in
                   mk1 uu____3148 in
                 (uu____3146, uu____3147, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____3141 in
             mk1 uu____3140
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____3172,t1) ->
             let uu____3178 =
               let uu____3179 =
                 let uu____3184 = resugar_term e in
                 let uu____3185 =
                   let uu____3186 =
                     let uu____3187 =
                       let uu____3193 =
                         let uu____3197 =
                           let uu____3200 = resugar_term t1 in
                           (uu____3200, FStar_Parser_AST.Nothing) in
                         [uu____3197] in
                       (name1, uu____3193) in
                     FStar_Parser_AST.Construct uu____3187 in
                   mk1 uu____3186 in
                 (uu____3184, uu____3185, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____3179 in
             mk1 uu____3178)
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
             let uu____3231 = FStar_Options.print_universes () in
             if uu____3231
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
             let uu____3267 = FStar_Options.print_universes () in
             if uu____3267
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
          let uu____3290 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____3290, FStar_Parser_AST.Nothing) in
        let uu____3291 = FStar_Options.print_effect_args () in
        if uu____3291
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___195_3332 =
                match uu___195_3332 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3374 -> aux l tl1
                     | uu____3379 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3403  ->
                 match uu____3403 with
                 | (e,uu____3409) ->
                     let uu____3410 = resugar_term e in
                     (uu____3410, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___196_3424 =
            match uu___196_3424 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3444 = resugar_term e in
                       (uu____3444, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3447 -> aux l tl1) in
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
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option
  =
  fun b  ->
    fun r  ->
      let uu____3472 = b in
      match uu____3472 with
      | (x,aq) ->
          let uu____3476 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____3476
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____3486 =
                     let uu____3487 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____3487 in
                   FStar_Parser_AST.mk_binder uu____3486 r
                     FStar_Parser_AST.Type_level imp
               | uu____3488 ->
                   let uu____3489 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____3489
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____3491 =
                        let uu____3492 =
                          let uu____3495 = bv_as_unique_ident x in
                          (uu____3495, e) in
                        FStar_Parser_AST.Annotated uu____3492 in
                      FStar_Parser_AST.mk_binder uu____3491 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3503 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3503 in
      let uu____3504 =
        let uu____3505 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3505.FStar_Syntax_Syntax.n in
      match uu____3504 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3511 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____3511
          else
            (let uu____3513 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3513
               (fun aq  ->
                  let uu____3521 =
                    let uu____3522 =
                      let uu____3523 =
                        let uu____3527 = bv_as_unique_ident x in
                        (uu____3527, aq) in
                      FStar_Parser_AST.PatVar uu____3523 in
                    mk1 uu____3522 in
                  FStar_Pervasives_Native.Some uu____3521))
      | uu____3529 ->
          let uu____3530 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3530
            (fun aq  ->
               let pat =
                 let uu____3541 =
                   let uu____3542 =
                     let uu____3546 = bv_as_unique_ident x in
                     (uu____3546, aq) in
                   FStar_Parser_AST.PatVar uu____3542 in
                 mk1 uu____3541 in
               let uu____3548 = FStar_Options.print_bound_var_types () in
               if uu____3548
               then
                 let uu____3550 =
                   let uu____3551 =
                     let uu____3552 =
                       let uu____3555 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3555) in
                     FStar_Parser_AST.PatAscribed uu____3552 in
                   mk1 uu____3551 in
                 FStar_Pervasives_Native.Some uu____3550
               else FStar_Pervasives_Native.Some pat)
and resugar_pat: FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
    let to_arg_qual bopt =
      FStar_Util.bind_opt bopt
        (fun b  ->
           if true
           then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
           else FStar_Pervasives_Native.None) in
    let rec aux p1 imp_opt =
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
              (fun uu____3608  ->
                 match uu____3608 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
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
              (fun uu____3630  ->
                 match uu____3630 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____3635 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3635
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3639;
             FStar_Syntax_Syntax.fv_delta = uu____3640;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3656 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3656 FStar_List.rev in
          let args1 =
            let uu____3666 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3678  ->
                      match uu____3678 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____3666 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3720 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3720
            | (hd1::tl1,hd2::tl2) ->
                let uu____3734 = map21 tl1 tl2 in (hd1, hd2) :: uu____3734 in
          let args2 =
            let uu____3744 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3744 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3773  ->
                 match uu____3773 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3780 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3780 with
           | FStar_Pervasives_Native.Some (op,uu____3785) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____3790 =
                 let uu____3791 =
                   let uu____3795 = bv_as_unique_ident v1 in
                   let uu____3796 = to_arg_qual imp_opt in
                   (uu____3795, uu____3796) in
                 FStar_Parser_AST.PatVar uu____3791 in
               mk1 uu____3790)
      | FStar_Syntax_Syntax.Pat_wild uu____3799 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3807 =
              let uu____3808 =
                let uu____3812 = bv_as_unique_ident bv in
                (uu____3812,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____3808 in
            mk1 uu____3807 in
          let uu____3814 = FStar_Options.print_bound_var_types () in
          if uu____3814
          then
            let uu____3815 =
              let uu____3816 =
                let uu____3819 = resugar_term term in (pat, uu____3819) in
              FStar_Parser_AST.PatAscribed uu____3816 in
            mk1 uu____3815
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___197_3825  ->
    match uu___197_3825 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3831 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3832 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____3833 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____3836 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____3841 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____3846 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___198_3850  ->
    match uu___198_3850 with
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
          (tylid,uvs,bs,t,uu____3872,datacons) ->
          let uu____3878 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3896,uu____3897,uu____3898,inductive_lid,uu____3900,uu____3901)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3904 -> failwith "unexpected")) in
          (match uu____3878 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3916 = FStar_Options.print_implicits () in
                 if uu____3916 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3924 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___199_3928  ->
                           match uu___199_3928 with
                           | FStar_Syntax_Syntax.RecordType uu____3929 ->
                               true
                           | uu____3934 -> false)) in
                 if uu____3924
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3962,univs1,term,uu____3965,num,uu____3967)
                         ->
                         let uu____3970 =
                           let uu____3971 = FStar_Syntax_Subst.compress term in
                           uu____3971.FStar_Syntax_Syntax.n in
                         (match uu____3970 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3980) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____4016  ->
                                        match uu____4016 with
                                        | (b,qual) ->
                                            let uu____4025 =
                                              let uu____4026 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____4026 in
                                            let uu____4027 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____4025, uu____4027,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____4033 -> failwith "unexpected")
                     | uu____4039 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____4106,num,uu____4108) ->
                          let c =
                            let uu____4118 =
                              let uu____4120 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____4120 in
                            ((l.FStar_Ident.ident), uu____4118,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____4129 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____4168 ->
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
        let uu____4185 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____4185;
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
      let uu____4202 = ts in
      match uu____4202 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____4208 =
            let uu____4209 =
              let uu____4216 =
                let uu____4221 =
                  let uu____4225 =
                    let uu____4226 =
                      let uu____4233 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____4233) in
                    FStar_Parser_AST.TyconAbbrev uu____4226 in
                  (uu____4225, FStar_Pervasives_Native.None) in
                [uu____4221] in
              (false, uu____4216) in
            FStar_Parser_AST.Tycon uu____4209 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____4208
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
            let uu____4277 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____4277 with
            | (bs,action_defn) ->
                let uu____4282 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____4282 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____4288 = FStar_Options.print_implicits () in
                       if uu____4288
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____4292 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____4292 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____4302 =
                           let uu____4308 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____4308,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____4302 in
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
          let uu____4347 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4347 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4353 = FStar_Options.print_implicits () in
                if uu____4353 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4357 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4357 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4400) ->
        let uu____4405 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4418 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4427 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4431 -> false
                  | uu____4439 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4405 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4459 se1 =
               match uu____4459 with
               | (datacon_ses1,tycons) ->
                   let uu____4474 = resugar_typ datacon_ses1 se1 in
                   (match uu____4474 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4483 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4483 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4502 =
                         let uu____4503 =
                           let uu____4504 =
                             let uu____4511 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____4511) in
                           FStar_Parser_AST.Tycon uu____4504 in
                         decl'_to_decl se uu____4503 in
                       FStar_Pervasives_Native.Some uu____4502
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4529,uu____4530,uu____4531,uu____4532,uu____4533)
                            ->
                            let uu____4536 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____4536
                        | uu____4538 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4540 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4544) ->
        let uu____4547 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___200_4552  ->
                  match uu___200_4552 with
                  | FStar_Syntax_Syntax.Projector (uu____4553,uu____4554) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4555 -> true
                  | uu____4556 -> false)) in
        if uu____4547
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4581) ->
               let uu____4588 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____4588
           | uu____4592 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4595,fml) ->
        let uu____4597 =
          let uu____4598 =
            let uu____4599 =
              let uu____4602 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4602) in
            FStar_Parser_AST.Assume uu____4599 in
          decl'_to_decl se uu____4598 in
        FStar_Pervasives_Native.Some uu____4597
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4604 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4604
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4606 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4606
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____4613,t) ->
              let uu____4620 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4620
          | uu____4621 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____4626,t) ->
              let uu____4633 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4633
          | uu____4634 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____4649 -> failwith "Should not happen hopefully" in
        let uu____4654 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____4654
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4662 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4662 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4669 = FStar_Options.print_implicits () in
               if uu____4669 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4676 =
               let uu____4677 =
                 let uu____4678 =
                   let uu____4685 =
                     let uu____4690 =
                       let uu____4694 =
                         let uu____4695 =
                           let uu____4702 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____4702) in
                         FStar_Parser_AST.TyconAbbrev uu____4695 in
                       (uu____4694, FStar_Pervasives_Native.None) in
                     [uu____4690] in
                   (false, uu____4685) in
                 FStar_Parser_AST.Tycon uu____4678 in
               decl'_to_decl se uu____4677 in
             FStar_Pervasives_Native.Some uu____4676)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4717 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____4717
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4721 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___201_4726  ->
                  match uu___201_4726 with
                  | FStar_Syntax_Syntax.Projector (uu____4727,uu____4728) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4729 -> true
                  | uu____4730 -> false)) in
        if uu____4721
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____4734 =
               (let uu____4737 = FStar_Options.print_universes () in
                Prims.op_Negation uu____4737) || (FStar_List.isEmpty uvs) in
             if uu____4734
             then resugar_term t
             else
               (let uu____4739 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____4739 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____4745 =
                      let uu____4746 =
                        let uu____4750 = resugar_term t1 in
                        (uu____4750, universes, true) in
                      FStar_Parser_AST.Labeled uu____4746 in
                    FStar_Parser_AST.mk_term uu____4745
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____4751 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____4751)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4752 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____4761 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____4769 -> FStar_Pervasives_Native.None