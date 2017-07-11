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
        let uu____543 = string_to_op s in
        (match uu____543 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____557 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____565 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____572 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____577 -> true
    | uu____578 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____607 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____607 in
    let var a r =
      let uu____615 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____615 in
    let uu____616 =
      let uu____617 = FStar_Syntax_Subst.compress t in
      uu____617.FStar_Syntax_Syntax.n in
    match uu____616 with
    | FStar_Syntax_Syntax.Tm_delayed uu____619 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____634 = let uu____636 = bv_as_unique_ident x in [uu____636] in
          FStar_Ident.lid_of_ids uu____634 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____639 = let uu____641 = bv_as_unique_ident x in [uu____641] in
          FStar_Ident.lid_of_ids uu____639 in
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
          let uu____665 =
            let uu____666 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____666 in
          mk1 uu____665
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
             | uu____679 -> failwith "wrong projector format")
          else
            (let uu____682 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____685 =
                    let uu____686 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____686 in
                  let uu____687 = FStar_String.get s (Prims.parse_int "0") in
                  uu____685 <> uu____687) in
             if uu____682
             then
               let uu____688 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____688
             else
               (let uu____690 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____690))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____695 = FStar_Options.print_universes () in
        if uu____695
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____702 =
                   let uu____703 =
                     let uu____707 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____707, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____703 in
                 mk1 uu____702) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____710 = FStar_Syntax_Syntax.is_teff t in
        if uu____710
        then
          let uu____711 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____711
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____714 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____714
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____715 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____715
         | uu____716 ->
             let uu____717 = FStar_Options.print_universes () in
             if uu____717
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____728 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____728))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____731) ->
        let uu____742 = FStar_Syntax_Subst.open_term xs body in
        (match uu____742 with
         | (xs1,body1) ->
             let xs2 =
               let uu____748 = FStar_Options.print_implicits () in
               if uu____748 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____758  ->
                       match uu____758 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____776 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____776 with
         | (xs1,body1) ->
             let xs2 =
               let uu____782 = FStar_Options.print_implicits () in
               if uu____782 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____787 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____787 FStar_List.rev in
             let rec aux body3 uu___189_801 =
               match uu___189_801 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____812 =
          let uu____815 =
            let uu____816 = FStar_Syntax_Syntax.mk_binder x in [uu____816] in
          FStar_Syntax_Subst.open_term uu____815 phi in
        (match uu____812 with
         | (x1,phi1) ->
             let b =
               let uu____820 =
                 let uu____822 = FStar_List.hd x1 in
                 resugar_binder uu____822 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____820 in
             let uu____825 =
               let uu____826 =
                 let uu____829 = resugar_term phi1 in (b, uu____829) in
               FStar_Parser_AST.Refine uu____826 in
             mk1 uu____825)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___190_853 =
          match uu___190_853 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____890 -> failwith "last of an empty list" in
        let rec last_two uu___191_910 =
          match uu___191_910 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____926::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____966::t1 -> last_two t1 in
        let rec last_three uu___192_989 =
          match uu___192_989 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1005::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1019::uu____1020::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1076::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1126  ->
                    match uu____1126 with
                    | (e2,qual) ->
                        let uu____1137 = resugar_term e2 in
                        (uu____1137, qual))) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1149  ->
                 match uu____1149 with
                 | (x,qual) ->
                     let uu____1157 =
                       let uu____1158 =
                         let uu____1162 = resugar_imp qual in
                         (acc, x, uu____1162) in
                       FStar_Parser_AST.App uu____1158 in
                     mk1 uu____1157) e2 args2 in
        let args1 =
          let uu____1168 = FStar_Options.print_implicits () in
          if uu____1168 then args else filter_imp args in
        let uu____1175 = resugar_term_as_op e in
        (match uu____1175 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1181) ->
             (match args1 with
              | (fst1,uu____1185)::(snd1,uu____1187)::rest ->
                  let e1 =
                    let uu____1204 =
                      let uu____1205 =
                        let uu____1209 =
                          let uu____1211 = resugar_term fst1 in
                          let uu____1212 =
                            let uu____1214 = resugar_term snd1 in
                            [uu____1214] in
                          uu____1211 :: uu____1212 in
                        ((FStar_Ident.id_of_text "*"), uu____1209) in
                      FStar_Parser_AST.Op uu____1205 in
                    mk1 uu____1204 in
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
         | FStar_Pervasives_Native.Some ("dtuple",uu____1245) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1266)::[] -> b
               | uu____1275 -> failwith "wrong arguments to dtuple" in
             let uu____1281 =
               let uu____1282 = FStar_Syntax_Subst.compress body in
               uu____1282.FStar_Syntax_Syntax.n in
             (match uu____1281 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1286) ->
                  let uu____1297 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1297 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1303 = FStar_Options.print_implicits () in
                         if uu____1303 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1312 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1325  ->
                            match uu____1325 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1335) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____1339) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____1342 = FStar_List.hd args1 in
             (match uu____1342 with
              | (t1,uu____1350) ->
                  let uu____1353 =
                    let uu____1354 = FStar_Syntax_Subst.compress t1 in
                    uu____1354.FStar_Syntax_Syntax.n in
                  (match uu____1353 with
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
             let uu____1381 =
               match new_args with
               | (a1,uu____1391)::(a2,uu____1393)::[] -> (a1, a2)
               | uu____1409 -> failwith "wrong arguments to try_with" in
             (match uu____1381 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1428 =
                      let uu____1429 = FStar_Syntax_Subst.compress term in
                      uu____1429.FStar_Syntax_Syntax.n in
                    match uu____1428 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1433) ->
                        let uu____1444 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1444 with | (x1,e2) -> e2)
                    | uu____1449 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1451 = decomp body in resugar_term uu____1451 in
                  let handler1 =
                    let uu____1453 = decomp handler in
                    resugar_term uu____1453 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1459,uu____1460,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1477,uu____1478,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1491 =
                          let uu____1492 =
                            let uu____1497 = resugar_body t11 in
                            (uu____1497, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1492 in
                        mk1 uu____1491
                    | uu____1499 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1532 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____1548) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____1552) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1603 -> (xs, pat, t1) in
             let resugar body =
               let uu____1611 =
                 let uu____1612 = FStar_Syntax_Subst.compress body in
                 uu____1612.FStar_Syntax_Syntax.n in
               match uu____1611 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1616) ->
                   let uu____1627 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1627 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1633 = FStar_Options.print_implicits () in
                          if uu____1633 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1640 =
                          let uu____1645 =
                            let uu____1646 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1646.FStar_Syntax_Syntax.n in
                          match uu____1645 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1686  ->
                                                 match uu____1686 with
                                                 | (e2,uu____1690) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1693) ->
                                    let uu____1694 =
                                      let uu____1696 =
                                        let uu____1697 = name s r in
                                        mk1 uu____1697 in
                                      [uu____1696] in
                                    [uu____1694]
                                | uu____1700 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1705 ->
                              let uu____1706 = resugar_term body2 in
                              ([], uu____1706) in
                        (match uu____1640 with
                         | (pats,body3) ->
                             let uu____1716 = uncurry xs3 pats body3 in
                             (match uu____1716 with
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
               | uu____1743 ->
                   if op = "forall"
                   then
                     let uu____1744 =
                       let uu____1745 =
                         let uu____1752 = resugar_term body in
                         ([], [[]], uu____1752) in
                       FStar_Parser_AST.QForall uu____1745 in
                     mk1 uu____1744
                   else
                     (let uu____1759 =
                        let uu____1760 =
                          let uu____1767 = resugar_term body in
                          ([], [[]], uu____1767) in
                        FStar_Parser_AST.QExists uu____1760 in
                      mk1 uu____1759) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1788)::[] -> resugar b
                | uu____1797 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____1803) ->
             let uu____1806 = FStar_List.hd args1 in
             (match uu____1806 with | (e1,uu____1814) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1842  ->
                       match uu____1842 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____1847 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1847 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1857 =
                         let uu____1858 =
                           let uu____1862 =
                             let uu____1864 = last1 args1 in
                             resugar uu____1864 in
                           (op1, uu____1862) in
                         FStar_Parser_AST.Op uu____1858 in
                       mk1 uu____1857
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1878 =
                         let uu____1879 =
                           let uu____1883 =
                             let uu____1885 = last_two args1 in
                             resugar uu____1885 in
                           (op1, uu____1883) in
                         FStar_Parser_AST.Op uu____1879 in
                       mk1 uu____1878
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1899 =
                         let uu____1900 =
                           let uu____1904 =
                             let uu____1906 = last_three args1 in
                             resugar uu____1906 in
                           (op1, uu____1904) in
                         FStar_Parser_AST.Op uu____1900 in
                       mk1 uu____1899
                   | uu____1911 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1921 =
                    let uu____1922 =
                      let uu____1926 =
                        let uu____1928 = last_two args1 in resugar uu____1928 in
                      (op1, uu____1926) in
                    FStar_Parser_AST.Op uu____1922 in
                  mk1 uu____1921
              | uu____1933 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1936,t1)::[]) ->
        let bnds =
          let uu____1974 =
            let uu____1977 = resugar_pat pat in
            let uu____1978 = resugar_term e in (uu____1977, uu____1978) in
          [uu____1974] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____1989,t1)::(pat2,uu____1992,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2041 =
          let uu____2042 =
            let uu____2046 = resugar_term e in
            let uu____2047 = resugar_term t1 in
            let uu____2048 = resugar_term t2 in
            (uu____2046, uu____2047, uu____2048) in
          FStar_Parser_AST.If uu____2042 in
        mk1 uu____2041
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2080 =
          match uu____2080 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____2099 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____2099 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2102 =
          let uu____2103 =
            let uu____2111 = resugar_term e in
            let uu____2112 = FStar_List.map resugar_branch branches in
            (uu____2111, uu____2112) in
          FStar_Parser_AST.Match uu____2103 in
        mk1 uu____2102
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2134) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2170 =
          let uu____2171 =
            let uu____2176 = resugar_term e in (uu____2176, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2171 in
        mk1 uu____2170
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2192 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2192 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2208 =
                 let uu____2211 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2211 in
               match uu____2208 with
               | (univs1,td) ->
                   let uu____2218 =
                     let uu____2223 =
                       let uu____2224 = FStar_Syntax_Subst.compress td in
                       uu____2224.FStar_Syntax_Syntax.n in
                     match uu____2223 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2230,(t1,uu____2232)::(d,uu____2234)::[]) ->
                         (t1, d)
                     | uu____2256 -> failwith "wrong let binding format" in
                   (match uu____2218 with
                    | (typ,def) ->
                        let uu____2271 =
                          let uu____2275 =
                            let uu____2276 = FStar_Syntax_Subst.compress def in
                            uu____2276.FStar_Syntax_Syntax.n in
                          match uu____2275 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2283) ->
                              let uu____2294 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2294 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2303 =
                                       FStar_Options.print_implicits () in
                                     if uu____2303 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2305 -> ([], def, false) in
                        (match uu____2271 with
                         | (binders,term,is_pat_app) ->
                             let uu____2319 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2326 =
                                     let uu____2327 =
                                       let uu____2328 =
                                         let uu____2332 =
                                           bv_as_unique_ident bv in
                                         (uu____2332,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____2328 in
                                     mk_pat uu____2327 in
                                   (uu____2326, term) in
                             (match uu____2319 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____2354  ->
                                              match uu____2354 with
                                              | (bv,q) ->
                                                  let uu____2363 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____2363
                                                    (fun q1  ->
                                                       let uu____2371 =
                                                         let uu____2372 =
                                                           let uu____2376 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____2376, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____2372 in
                                                       mk_pat uu____2371))) in
                                    let uu____2378 =
                                      let uu____2381 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2381) in
                                    let uu____2383 =
                                      universe_to_string univs1 in
                                    (uu____2378, uu____2383)
                                  else
                                    (let uu____2387 =
                                       let uu____2390 = resugar_term term1 in
                                       (pat, uu____2390) in
                                     let uu____2391 =
                                       universe_to_string univs1 in
                                     (uu____2387, uu____2391))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____2417 =
                   let uu____2418 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____2418 in
                 Obj.magic
                   (if uu____2417
                    then FStar_Pervasives_Native.fst
                    else
                      (fun uu___193_2430  ->
                         match uu___193_2430 with
                         | ((pat,body2),univs1) ->
                             let uu____2442 =
                               if univs1 = ""
                               then body2
                               else
                                 mk1
                                   (FStar_Parser_AST.Labeled
                                      (body2, univs1, true)) in
                             (pat, uu____2442))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2456) ->
        let s =
          let uu____2470 =
            let uu____2471 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2471 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2470 in
        let uu____2472 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2472
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___194_2480 =
          match uu___194_2480 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____2493 =
                  let uu____2494 = FStar_Syntax_Subst.compress h in
                  uu____2494.FStar_Syntax_Syntax.n in
                match uu____2493 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____2505 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____2505, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____2518 = head_fv_universes_args h1 in
                    (match uu____2518 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____2565 = head_fv_universes_args head1 in
                    (match uu____2565 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____2603 ->
                    let uu____2604 =
                      let uu____2605 =
                        let uu____2606 =
                          let uu____2607 = resugar_term h in
                          parser_term_to_string uu____2607 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____2606 in
                      FStar_Errors.Err uu____2605 in
                    raise uu____2604 in
              let uu____2616 =
                try
                  let uu____2644 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____2644
                with
                | FStar_Errors.Err uu____2657 ->
                    let uu____2658 =
                      let uu____2659 =
                        let uu____2662 =
                          let uu____2663 =
                            let uu____2664 = resugar_term e in
                            parser_term_to_string uu____2664 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____2663 in
                        (uu____2662, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____2659 in
                    raise uu____2658 in
              (match uu____2616 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____2695 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____2695, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.map
                       (fun uu____2710  ->
                          match uu____2710 with
                          | (t1,q) ->
                              let uu____2720 = resugar_term t1 in
                              let uu____2721 = resugar_imp q in
                              (uu____2720, uu____2721)) args in
                   let args2 =
                     let uu____2726 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____2728 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____2728) in
                     if uu____2726
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2743,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2759 =
                      let uu____2760 =
                        let uu____2765 = resugar_seq t11 in
                        (uu____2765, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2760 in
                    mk1 uu____2759
                | uu____2767 -> t1 in
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
               | uu____2780 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____2782 =
                let uu____2783 = FStar_Syntax_Subst.compress e in
                uu____2783.FStar_Syntax_Syntax.n in
              (match uu____2782 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____2786;
                      FStar_Syntax_Syntax.vars = uu____2787;_},(term,uu____2789)::[])
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
         | FStar_Syntax_Syntax.Meta_alien (uu____2841,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2848 =
               let uu____2849 =
                 let uu____2854 = resugar_term e in
                 let uu____2855 =
                   let uu____2856 =
                     let uu____2857 =
                       let uu____2863 =
                         let uu____2867 =
                           let uu____2870 = resugar_term t1 in
                           (uu____2870, FStar_Parser_AST.Nothing) in
                         [uu____2867] in
                       (name1, uu____2863) in
                     FStar_Parser_AST.Construct uu____2857 in
                   mk1 uu____2856 in
                 (uu____2854, uu____2855, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2849 in
             mk1 uu____2848
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2880,t1) ->
             let uu____2884 =
               let uu____2885 =
                 let uu____2890 = resugar_term e in
                 let uu____2891 =
                   let uu____2892 =
                     let uu____2893 =
                       let uu____2899 =
                         let uu____2903 =
                           let uu____2906 = resugar_term t1 in
                           (uu____2906, FStar_Parser_AST.Nothing) in
                         [uu____2903] in
                       (name1, uu____2899) in
                     FStar_Parser_AST.Construct uu____2893 in
                   mk1 uu____2892 in
                 (uu____2890, uu____2891, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____2885 in
             mk1 uu____2884)
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
             let uu____2935 = FStar_Options.print_universes () in
             if uu____2935
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
             let uu____2969 = FStar_Options.print_universes () in
             if uu____2969
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
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___195_3029 =
                match uu___195_3029 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3062 -> aux l tl1
                     | uu____3066 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3087  ->
                 match uu____3087 with
                 | (e,uu____3093) ->
                     let uu____3094 = resugar_term e in
                     (uu____3094, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___196_3108 =
            match uu___196_3108 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3127 = resugar_term e in
                       (uu____3127, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3130 -> aux l tl1) in
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
      let uu____3155 = b in
      match uu____3155 with
      | (x,aq) ->
          let uu____3159 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____3159
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____3169 =
                     let uu____3170 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____3170 in
                   FStar_Parser_AST.mk_binder uu____3169 r
                     FStar_Parser_AST.Type_level imp
               | uu____3171 ->
                   let uu____3172 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____3172
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____3174 =
                        let uu____3175 =
                          let uu____3178 = bv_as_unique_ident x in
                          (uu____3178, e) in
                        FStar_Parser_AST.Annotated uu____3175 in
                      FStar_Parser_AST.mk_binder uu____3174 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3186 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3186 in
      let uu____3187 =
        let uu____3188 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3188.FStar_Syntax_Syntax.n in
      match uu____3187 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3193 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____3193
          else
            (let uu____3195 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3195
               (fun aq  ->
                  let uu____3203 =
                    let uu____3204 =
                      let uu____3205 =
                        let uu____3209 = bv_as_unique_ident x in
                        (uu____3209, aq) in
                      FStar_Parser_AST.PatVar uu____3205 in
                    mk1 uu____3204 in
                  FStar_Pervasives_Native.Some uu____3203))
      | uu____3211 ->
          let uu____3212 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3212
            (fun aq  ->
               let pat =
                 let uu____3223 =
                   let uu____3224 =
                     let uu____3228 = bv_as_unique_ident x in
                     (uu____3228, aq) in
                   FStar_Parser_AST.PatVar uu____3224 in
                 mk1 uu____3223 in
               let uu____3230 = FStar_Options.print_bound_var_types () in
               if uu____3230
               then
                 let uu____3232 =
                   let uu____3233 =
                     let uu____3234 =
                       let uu____3237 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3237) in
                     FStar_Parser_AST.PatAscribed uu____3234 in
                   mk1 uu____3233 in
                 FStar_Pervasives_Native.Some uu____3232
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
              (fun uu____3290  ->
                 match uu____3290 with
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
              (fun uu____3312  ->
                 match uu____3312 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____3317 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3317
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3321;
             FStar_Syntax_Syntax.fv_delta = uu____3322;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3338 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3338 FStar_List.rev in
          let args1 =
            let uu____3348 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3360  ->
                      match uu____3360 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____3348 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3402 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3402
            | (hd1::tl1,hd2::tl2) ->
                let uu____3416 = map21 tl1 tl2 in (hd1, hd2) :: uu____3416 in
          let args2 =
            let uu____3426 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3426 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3455  ->
                 match uu____3455 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3462 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3462 with
           | FStar_Pervasives_Native.Some (op,uu____3467) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____3472 =
                 let uu____3473 =
                   let uu____3477 = bv_as_unique_ident v1 in
                   let uu____3478 = to_arg_qual imp_opt in
                   (uu____3477, uu____3478) in
                 FStar_Parser_AST.PatVar uu____3473 in
               mk1 uu____3472)
      | FStar_Syntax_Syntax.Pat_wild uu____3481 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3487 =
              let uu____3488 =
                let uu____3492 = bv_as_unique_ident bv in
                (uu____3492,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____3488 in
            mk1 uu____3487 in
          let uu____3494 = FStar_Options.print_bound_var_types () in
          if uu____3494
          then
            let uu____3495 =
              let uu____3496 =
                let uu____3499 = resugar_term term in (pat, uu____3499) in
              FStar_Parser_AST.PatAscribed uu____3496 in
            mk1 uu____3495
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___197_3505  ->
    match uu___197_3505 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3511 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3512 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____3513 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____3516 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____3521 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____3526 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___198_3530  ->
    match uu___198_3530 with
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
          (tylid,uvs,bs,t,uu____3552,datacons) ->
          let uu____3558 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3576,uu____3577,uu____3578,inductive_lid,uu____3580,uu____3581)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3584 -> failwith "unexpected")) in
          (match uu____3558 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3596 = FStar_Options.print_implicits () in
                 if uu____3596 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3604 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___199_3608  ->
                           match uu___199_3608 with
                           | FStar_Syntax_Syntax.RecordType uu____3609 ->
                               true
                           | uu____3614 -> false)) in
                 if uu____3604
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3642,univs1,term,uu____3645,num,uu____3647)
                         ->
                         let uu____3650 =
                           let uu____3651 = FStar_Syntax_Subst.compress term in
                           uu____3651.FStar_Syntax_Syntax.n in
                         (match uu____3650 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3659) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3693  ->
                                        match uu____3693 with
                                        | (b,qual) ->
                                            let uu____3702 =
                                              let uu____3703 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3703 in
                                            let uu____3704 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3702, uu____3704,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____3710 -> failwith "unexpected")
                     | uu____3716 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____3783,num,uu____3785) ->
                          let c =
                            let uu____3795 =
                              let uu____3797 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____3797 in
                            ((l.FStar_Ident.ident), uu____3795,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____3806 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____3845 ->
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
        let uu____3862 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____3862;
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
      let uu____3879 = ts in
      match uu____3879 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3885 =
            let uu____3886 =
              let uu____3893 =
                let uu____3898 =
                  let uu____3902 =
                    let uu____3903 =
                      let uu____3910 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____3910) in
                    FStar_Parser_AST.TyconAbbrev uu____3903 in
                  (uu____3902, FStar_Pervasives_Native.None) in
                [uu____3898] in
              (false, uu____3893) in
            FStar_Parser_AST.Tycon uu____3886 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3885
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
            let uu____3954 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3954 with
            | (bs,action_defn) ->
                let uu____3959 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3959 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3965 = FStar_Options.print_implicits () in
                       if uu____3965
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3969 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3969 FStar_List.rev in
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
                    (map_opt (fun b  -> resugar_binder b r)) in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4077) ->
        let uu____4082 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4095 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4104 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4108 -> false
                  | uu____4116 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4082 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4136 se1 =
               match uu____4136 with
               | (datacon_ses1,tycons) ->
                   let uu____4151 = resugar_typ datacon_ses1 se1 in
                   (match uu____4151 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4160 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4160 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4179 =
                         let uu____4180 =
                           let uu____4181 =
                             let uu____4188 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____4188) in
                           FStar_Parser_AST.Tycon uu____4181 in
                         decl'_to_decl se uu____4180 in
                       FStar_Pervasives_Native.Some uu____4179
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4206,uu____4207,uu____4208,uu____4209,uu____4210)
                            ->
                            let uu____4213 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____4213
                        | uu____4215 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4217 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4221) ->
        let uu____4224 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___200_4229  ->
                  match uu___200_4229 with
                  | FStar_Syntax_Syntax.Projector (uu____4230,uu____4231) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4232 -> true
                  | uu____4233 -> false)) in
        if uu____4224
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
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4267,fml) ->
        let uu____4269 =
          let uu____4270 =
            let uu____4271 =
              let uu____4274 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4274) in
            FStar_Parser_AST.Assume uu____4271 in
          decl'_to_decl se uu____4270 in
        FStar_Pervasives_Native.Some uu____4269
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4276 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4276
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4278 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____4278
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____4285,t) ->
              let uu____4292 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4292
          | uu____4293 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____4298,t) ->
              let uu____4305 = resugar_term t in
              FStar_Pervasives_Native.Some uu____4305
          | uu____4306 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____4321 -> failwith "Should not happen hopefully" in
        let uu____4326 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____4326
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4334 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4334 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4341 = FStar_Options.print_implicits () in
               if uu____4341 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4348 =
               let uu____4349 =
                 let uu____4350 =
                   let uu____4357 =
                     let uu____4362 =
                       let uu____4366 =
                         let uu____4367 =
                           let uu____4374 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____4374) in
                         FStar_Parser_AST.TyconAbbrev uu____4367 in
                       (uu____4366, FStar_Pervasives_Native.None) in
                     [uu____4362] in
                   (false, uu____4357) in
                 FStar_Parser_AST.Tycon uu____4350 in
               decl'_to_decl se uu____4349 in
             FStar_Pervasives_Native.Some uu____4348)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4389 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____4389
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4393 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___201_4398  ->
                  match uu___201_4398 with
                  | FStar_Syntax_Syntax.Projector (uu____4399,uu____4400) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4401 -> true
                  | uu____4402 -> false)) in
        if uu____4393
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____4406 =
               (let uu____4409 = FStar_Options.print_universes () in
                Prims.op_Negation uu____4409) || (FStar_List.isEmpty uvs) in
             if uu____4406
             then resugar_term t
             else
               (let uu____4411 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____4411 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____4417 =
                      let uu____4418 =
                        let uu____4422 = resugar_term t1 in
                        (uu____4422, universes, true) in
                      FStar_Parser_AST.Labeled uu____4418 in
                    FStar_Parser_AST.mk_term uu____4417
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____4423 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____4423)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4424 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____4433 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____4441 -> FStar_Pervasives_Native.None