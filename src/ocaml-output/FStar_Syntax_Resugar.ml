open Prims
let doc_to_string: FStar_Pprint.document -> Prims.string =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
let parser_term_to_string: FStar_Parser_AST.term -> Prims.string =
  fun t  ->
    let uu____7 = FStar_Parser_ToDocument.term_to_document t in
    doc_to_string uu____7
let map_opt f l =
  let uu____37 =
    FStar_Util.choose_map
      (fun uu____44  -> fun x  -> let uu____46 = f x in ((), uu____46)) () l in
  FStar_Pervasives_Native.snd uu____37
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____57 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____57
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___183_112  ->
          match uu___183_112 with
          | (uu____119,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____120)) -> false
          | uu____123 -> true))
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
      | uu____185 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____193 = FStar_Options.print_universes () in
    if uu____193
    then
      let uu____194 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____194 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____224 ->
          let uu____225 = universe_to_int (Prims.parse_int "0") u in
          (match uu____225 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____232 =
                      let uu____233 =
                        let uu____234 =
                          let uu____245 = FStar_Util.string_of_int n1 in
                          (uu____245, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____234 in
                      FStar_Parser_AST.Const uu____233 in
                    mk1 uu____232 r
                | uu____256 ->
                    let e1 =
                      let uu____258 =
                        let uu____259 =
                          let uu____260 =
                            let uu____271 = FStar_Util.string_of_int n1 in
                            (uu____271, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____260 in
                        FStar_Parser_AST.Const uu____259 in
                      mk1 uu____258 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____288 ->
               let t =
                 let uu____292 =
                   let uu____293 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____293 in
                 mk1 uu____292 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____296 =
                        let uu____297 =
                          let uu____304 = resugar_universe x r in
                          (acc, uu____304, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____297 in
                      mk1 uu____296 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____306 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____313 =
              let uu____318 =
                let uu____319 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____319 in
              (uu____318, r) in
            FStar_Ident.mk_ident uu____313 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___184_338 =
      match uu___184_338 with
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
      | uu____413 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____440 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____450 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____450 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____458 ->
               let op =
                 let uu____462 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____492) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____462 in
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
      let uu____678 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____678 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____725 ->
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
                (let uu____785 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____785
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____805 =
      let uu____806 = FStar_Syntax_Subst.compress t in
      uu____806.FStar_Syntax_Syntax.n in
    match uu____805 with
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
        let uu____838 = string_to_op s in
        (match uu____838 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____864 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____881 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____889 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____893 -> true
    | uu____894 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____925 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____925 in
    let var a r =
      let uu____933 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____933 in
    let uu____934 =
      let uu____935 = FStar_Syntax_Subst.compress t in
      uu____935.FStar_Syntax_Syntax.n in
    match uu____934 with
    | FStar_Syntax_Syntax.Tm_delayed uu____940 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____981 = let uu____984 = bv_as_unique_ident x in [uu____984] in
          FStar_Ident.lid_of_ids uu____981 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____987 = let uu____990 = bv_as_unique_ident x in [uu____990] in
          FStar_Ident.lid_of_ids uu____987 in
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
          let uu____1011 =
            let uu____1012 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____1012 in
          mk1 uu____1011
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
             | uu____1022 -> failwith "wrong projector format")
          else
            (let uu____1026 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1027 =
                    let uu____1028 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1028 in
                  let uu____1029 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1027 <> uu____1029) in
             if uu____1026
             then
               let uu____1030 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1030
             else
               (let uu____1032 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1032))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1043 = FStar_Options.print_universes () in
        if uu____1043
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1047 =
                   let uu____1048 =
                     let uu____1055 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1055, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1048 in
                 mk1 uu____1047) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1058 = FStar_Syntax_Syntax.is_teff t in
        if uu____1058
        then
          let uu____1059 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1059
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1062 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1062
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1063 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1063
         | uu____1064 ->
             let uu____1065 = FStar_Options.print_universes () in
             if uu____1065
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1083 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1083))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1086) ->
        let uu____1131 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1131 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1139 = FStar_Options.print_implicits () in
               if uu____1139 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1150  ->
                       match uu____1150 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1184 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1184 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1192 = FStar_Options.print_implicits () in
               if uu____1192 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1198 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1198 FStar_List.rev in
             let rec aux body3 uu___185_1216 =
               match uu___185_1216 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1236 =
          let uu____1241 =
            let uu____1242 = FStar_Syntax_Syntax.mk_binder x in [uu____1242] in
          FStar_Syntax_Subst.open_term uu____1241 phi in
        (match uu____1236 with
         | (x1,phi1) ->
             let b =
               let uu____1246 =
                 let uu____1249 = FStar_List.hd x1 in
                 resugar_binder uu____1249 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1246 in
             let uu____1254 =
               let uu____1255 =
                 let uu____1260 = resugar_term phi1 in (b, uu____1260) in
               FStar_Parser_AST.Refine uu____1255 in
             mk1 uu____1254)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___186_1314 =
          match uu___186_1314 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1404 -> failwith "last of an empty list" in
        let rec last_two uu___187_1448 =
          match uu___187_1448 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1487::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1588::t1 -> last_two t1 in
        let rec last_three uu___188_1639 =
          match uu___188_1639 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1678::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1713::uu____1714::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1856::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1944  ->
                    match uu____1944 with
                    | (e2,qual) ->
                        let uu____1963 = resugar_term e2 in
                        (uu____1963, qual))) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1974  ->
                 match uu____1974 with
                 | (x,qual) ->
                     let uu____1987 =
                       let uu____1988 =
                         let uu____1995 = resugar_imp qual in
                         (acc, x, uu____1995) in
                       FStar_Parser_AST.App uu____1988 in
                     mk1 uu____1987) e2 args2 in
        let args1 =
          let uu____2007 = FStar_Options.print_implicits () in
          if uu____2007 then args else filter_imp args in
        let uu____2023 = resugar_term_as_op e in
        (match uu____2023 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____2034) ->
             (match args1 with
              | (fst1,uu____2040)::(snd1,uu____2042)::rest ->
                  let e1 =
                    let uu____2087 =
                      let uu____2088 =
                        let uu____2095 =
                          let uu____2098 = resugar_term fst1 in
                          let uu____2099 =
                            let uu____2102 = resugar_term snd1 in
                            [uu____2102] in
                          uu____2098 :: uu____2099 in
                        ((FStar_Ident.id_of_text "*"), uu____2095) in
                      FStar_Parser_AST.Op uu____2088 in
                    mk1 uu____2087 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____2110  ->
                         match uu____2110 with
                         | (x,uu____2116) ->
                             let uu____2117 =
                               let uu____2118 =
                                 let uu____2125 =
                                   let uu____2128 =
                                     let uu____2131 = resugar_term x in
                                     [uu____2131] in
                                   e1 :: uu____2128 in
                                 ((FStar_Ident.id_of_text "*"), uu____2125) in
                               FStar_Parser_AST.Op uu____2118 in
                             mk1 uu____2117) e1 rest
              | uu____2134 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2145) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2179)::[] -> b
               | uu____2204 -> failwith "wrong arguments to dtuple" in
             let uu____2219 =
               let uu____2220 = FStar_Syntax_Subst.compress body in
               uu____2220.FStar_Syntax_Syntax.n in
             (match uu____2219 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2227) ->
                  let uu____2272 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2272 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2280 = FStar_Options.print_implicits () in
                         if uu____2280 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2291 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2311  ->
                            match uu____2311 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2321) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2327) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2332 = FStar_List.hd args1 in
             (match uu____2332 with
              | (t1,uu____2350) ->
                  let uu____2359 =
                    let uu____2360 = FStar_Syntax_Subst.compress t1 in
                    uu____2360.FStar_Syntax_Syntax.n in
                  (match uu____2359 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2375 =
                         let uu____2376 =
                           let uu____2381 = resugar_term t1 in
                           (uu____2381, f) in
                         FStar_Parser_AST.Project uu____2376 in
                       mk1 uu____2375
                   | uu____2382 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2383) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2407 =
               match new_args with
               | (a1,uu____2433)::(a2,uu____2435)::[] -> (a1, a2)
               | uu____2484 -> failwith "wrong arguments to try_with" in
             (match uu____2407 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2529 =
                      let uu____2530 = FStar_Syntax_Subst.compress term in
                      uu____2530.FStar_Syntax_Syntax.n in
                    match uu____2529 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2537) ->
                        let uu____2582 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2582 with | (x1,e2) -> e2)
                    | uu____2589 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2591 = decomp body in resugar_term uu____2591 in
                  let handler1 =
                    let uu____2593 = decomp handler in
                    resugar_term uu____2593 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2599,uu____2600,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2632,uu____2633,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2654 =
                          let uu____2655 =
                            let uu____2664 = resugar_body t11 in
                            (uu____2664, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2655 in
                        mk1 uu____2654
                    | uu____2667 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2722 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2752) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2758) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2843 -> (xs, pat, t1) in
             let resugar body =
               let uu____2854 =
                 let uu____2855 = FStar_Syntax_Subst.compress body in
                 uu____2855.FStar_Syntax_Syntax.n in
               match uu____2854 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2862) ->
                   let uu____2907 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2907 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2915 = FStar_Options.print_implicits () in
                          if uu____2915 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2923 =
                          let uu____2932 =
                            let uu____2933 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2933.FStar_Syntax_Syntax.n in
                          match uu____2932 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____3006  ->
                                                 match uu____3006 with
                                                 | (e2,uu____3012) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____3015) ->
                                    let uu____3016 =
                                      let uu____3019 =
                                        let uu____3020 = name s r in
                                        mk1 uu____3020 in
                                      [uu____3019] in
                                    [uu____3016]
                                | uu____3025 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____3034 ->
                              let uu____3035 = resugar_term body2 in
                              ([], uu____3035) in
                        (match uu____2923 with
                         | (pats,body3) ->
                             let uu____3052 = uncurry xs3 pats body3 in
                             (match uu____3052 with
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
               | uu____3100 ->
                   if op = "forall"
                   then
                     let uu____3101 =
                       let uu____3102 =
                         let uu____3115 = resugar_term body in
                         ([], [[]], uu____3115) in
                       FStar_Parser_AST.QForall uu____3102 in
                     mk1 uu____3101
                   else
                     (let uu____3127 =
                        let uu____3128 =
                          let uu____3141 = resugar_term body in
                          ([], [[]], uu____3141) in
                        FStar_Parser_AST.QExists uu____3128 in
                      mk1 uu____3127) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____3172)::[] -> resugar b
                | uu____3197 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____3209) ->
             let uu____3214 = FStar_List.hd args1 in
             (match uu____3214 with | (e1,uu____3232) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____3278  ->
                       match uu____3278 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____3285 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____3285 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____3294 =
                         let uu____3295 =
                           let uu____3302 =
                             let uu____3305 = last1 args1 in
                             resugar uu____3305 in
                           (op1, uu____3302) in
                         FStar_Parser_AST.Op uu____3295 in
                       mk1 uu____3294
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____3322 =
                         let uu____3323 =
                           let uu____3330 =
                             let uu____3333 = last_two args1 in
                             resugar uu____3333 in
                           (op1, uu____3330) in
                         FStar_Parser_AST.Op uu____3323 in
                       mk1 uu____3322
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3350 =
                         let uu____3351 =
                           let uu____3358 =
                             let uu____3361 = last_three args1 in
                             resugar uu____3361 in
                           (op1, uu____3358) in
                         FStar_Parser_AST.Op uu____3351 in
                       mk1 uu____3350
                   | uu____3370 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3379 =
                    let uu____3380 =
                      let uu____3387 =
                        let uu____3390 = last_two args1 in resugar uu____3390 in
                      (op1, uu____3387) in
                    FStar_Parser_AST.Op uu____3380 in
                  mk1 uu____3379
              | uu____3399 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3402,t1)::[]) ->
        let bnds =
          let uu____3509 =
            let uu____3514 = resugar_pat pat in
            let uu____3515 = resugar_term e in (uu____3514, uu____3515) in
          [uu____3509] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3533,t1)::(pat2,uu____3536,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3684 =
          let uu____3685 =
            let uu____3692 = resugar_term e in
            let uu____3693 = resugar_term t1 in
            let uu____3694 = resugar_term t2 in
            (uu____3692, uu____3693, uu____3694) in
          FStar_Parser_AST.If uu____3685 in
        mk1 uu____3684
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3768 =
          match uu____3768 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3799 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3799 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3803 =
          let uu____3804 =
            let uu____3819 = resugar_term e in
            let uu____3820 = FStar_List.map resugar_branch branches in
            (uu____3819, uu____3820) in
          FStar_Parser_AST.Match uu____3804 in
        mk1 uu____3803
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3860) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3961 =
          let uu____3962 =
            let uu____3971 = resugar_term e in (uu____3971, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3962 in
        mk1 uu____3961
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3999 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3999 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____4024 =
                 let uu____4029 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____4029 in
               match uu____4024 with
               | (univs1,td) ->
                   let uu____4040 =
                     let uu____4053 =
                       let uu____4054 = FStar_Syntax_Subst.compress td in
                       uu____4054.FStar_Syntax_Syntax.n in
                     match uu____4053 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____4071,(t1,uu____4073)::(d,uu____4075)::[]) ->
                         (t1, d)
                     | uu____4142 -> failwith "wrong let binding format" in
                   (match uu____4040 with
                    | (typ,def) ->
                        let uu____4181 =
                          let uu____4188 =
                            let uu____4189 = FStar_Syntax_Subst.compress def in
                            uu____4189.FStar_Syntax_Syntax.n in
                          match uu____4188 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4202) ->
                              let uu____4247 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____4247 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____4261 =
                                       FStar_Options.print_implicits () in
                                     if uu____4261 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____4263 -> ([], def, false) in
                        (match uu____4181 with
                         | (binders,term,is_pat_app) ->
                             let uu____4289 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____4304 =
                                     let uu____4305 =
                                       let uu____4306 =
                                         let uu____4313 =
                                           bv_as_unique_ident bv in
                                         (uu____4313,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____4306 in
                                     mk_pat uu____4305 in
                                   (uu____4304, term) in
                             (match uu____4289 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____4345  ->
                                              match uu____4345 with
                                              | (bv,q) ->
                                                  let uu____4360 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____4360
                                                    (fun q1  ->
                                                       let uu____4370 =
                                                         let uu____4371 =
                                                           let uu____4378 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____4378, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____4371 in
                                                       mk_pat uu____4370))) in
                                    let uu____4381 =
                                      let uu____4386 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____4386) in
                                    let uu____4389 =
                                      universe_to_string univs1 in
                                    (uu____4381, uu____4389)
                                  else
                                    (let uu____4395 =
                                       let uu____4400 = resugar_term term1 in
                                       (pat, uu____4400) in
                                     let uu____4401 =
                                       universe_to_string univs1 in
                                     (uu____4395, uu____4401))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____4447 =
                   let uu____4448 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____4448 in
                 Obj.magic
                   (if uu____4447
                    then FStar_Pervasives_Native.fst
                    else
                      (fun uu___189_4468  ->
                         match uu___189_4468 with
                         | ((pat,body2),univs1) ->
                             let uu____4488 =
                               if univs1 = ""
                               then body2
                               else
                                 mk1
                                   (FStar_Parser_AST.Labeled
                                      (body2, univs1, true)) in
                             (pat, uu____4488))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____4511) ->
        let s =
          let uu____4537 =
            let uu____4538 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____4538 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____4537 in
        let uu____4545 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____4545
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___190_4559 =
          match uu___190_4559 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4582 =
                  let uu____4583 = FStar_Syntax_Subst.compress h in
                  uu____4583.FStar_Syntax_Syntax.n in
                match uu____4582 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4607 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4607, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4638 = head_fv_universes_args h1 in
                    (match uu____4638 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4744 = head_fv_universes_args head1 in
                    (match uu____4744 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4828 ->
                    let uu____4829 =
                      let uu____4830 =
                        let uu____4831 =
                          let uu____4832 = resugar_term h in
                          parser_term_to_string uu____4832 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4831 in
                      FStar_Errors.Err uu____4830 in
                    raise uu____4829 in
              let uu____4851 =
                try
                  let uu____4907 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4907
                with
                | FStar_Errors.Err uu____4927 ->
                    let uu____4928 =
                      let uu____4929 =
                        let uu____4934 =
                          let uu____4935 =
                            let uu____4936 = resugar_term e in
                            parser_term_to_string uu____4936 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4935 in
                        (uu____4934, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4929 in
                    raise uu____4928 in
              (match uu____4851 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4994 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4994, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.map
                       (fun uu____5012  ->
                          match uu____5012 with
                          | (t1,q) ->
                              let uu____5029 = resugar_term t1 in
                              let uu____5030 = resugar_imp q in
                              (uu____5029, uu____5030)) args in
                   let args2 =
                     let uu____5038 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____5039 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____5039) in
                     if uu____5038
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____5062,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____5087 =
                      let uu____5088 =
                        let uu____5097 = resugar_seq t11 in
                        (uu____5097, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____5088 in
                    mk1 uu____5087
                | uu____5100 -> t1 in
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
               | uu____5122 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____5124 =
                let uu____5125 = FStar_Syntax_Subst.compress e in
                uu____5125.FStar_Syntax_Syntax.n in
              (match uu____5124 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____5131;
                      FStar_Syntax_Syntax.pos = uu____5132;
                      FStar_Syntax_Syntax.vars = uu____5133;_},(term,uu____5135)::[])
                   -> resugar_term term
               | uu____5178 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____5219  ->
                       match uu____5219 with
                       | (x,uu____5225) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____5227,p) ->
             let uu____5229 =
               let uu____5230 =
                 let uu____5237 = resugar_term e in (uu____5237, l, p) in
               FStar_Parser_AST.Labeled uu____5230 in
             mk1 uu____5229
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____5250 =
               let uu____5251 =
                 let uu____5260 = resugar_term e in
                 let uu____5261 =
                   let uu____5262 =
                     let uu____5263 =
                       let uu____5274 =
                         let uu____5281 =
                           let uu____5286 = resugar_term t1 in
                           (uu____5286, FStar_Parser_AST.Nothing) in
                         [uu____5281] in
                       (name1, uu____5274) in
                     FStar_Parser_AST.Construct uu____5263 in
                   mk1 uu____5262 in
                 (uu____5260, uu____5261, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____5251 in
             mk1 uu____5250
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5304,t1) ->
             let uu____5314 =
               let uu____5315 =
                 let uu____5324 = resugar_term e in
                 let uu____5325 =
                   let uu____5326 =
                     let uu____5327 =
                       let uu____5338 =
                         let uu____5345 =
                           let uu____5350 = resugar_term t1 in
                           (uu____5350, FStar_Parser_AST.Nothing) in
                         [uu____5345] in
                       (name1, uu____5338) in
                     FStar_Parser_AST.Construct uu____5327 in
                   mk1 uu____5326 in
                 (uu____5324, uu____5325, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____5315 in
             mk1 uu____5314)
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
             let uu____5402 = FStar_Options.print_universes () in
             if uu____5402
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
             let uu____5467 = FStar_Options.print_universes () in
             if uu____5467
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
          let uu____5508 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____5508, FStar_Parser_AST.Nothing) in
        let uu____5509 = FStar_Options.print_effect_args () in
        if uu____5509
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___191_5575 =
                match uu___191_5575 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____5654 -> aux l tl1
                     | uu____5663 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5700  ->
                 match uu____5700 with
                 | (e,uu____5710) ->
                     let uu____5711 = resugar_term e in
                     (uu____5711, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___192_5732 =
            match uu___192_5732 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5767 = resugar_term e in
                       (uu____5767, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5772 -> aux l tl1) in
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
      let uu____5817 = b in
      match uu____5817 with
      | (x,aq) ->
          let uu____5822 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5822
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5833 =
                     let uu____5834 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5834 in
                   FStar_Parser_AST.mk_binder uu____5833 r
                     FStar_Parser_AST.Type_level imp
               | uu____5835 ->
                   let uu____5836 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5836
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5838 =
                        let uu____5839 =
                          let uu____5844 = bv_as_unique_ident x in
                          (uu____5844, e) in
                        FStar_Parser_AST.Annotated uu____5839 in
                      FStar_Parser_AST.mk_binder uu____5838 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5853 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5853 in
      let uu____5854 =
        let uu____5855 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5855.FStar_Syntax_Syntax.n in
      match uu____5854 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5865 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5865
          else
            (let uu____5867 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5867
               (fun aq  ->
                  let uu____5877 =
                    let uu____5878 =
                      let uu____5879 =
                        let uu____5886 = bv_as_unique_ident x in
                        (uu____5886, aq) in
                      FStar_Parser_AST.PatVar uu____5879 in
                    mk1 uu____5878 in
                  FStar_Pervasives_Native.Some uu____5877))
      | uu____5889 ->
          let uu____5890 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5890
            (fun aq  ->
               let pat =
                 let uu____5901 =
                   let uu____5902 =
                     let uu____5909 = bv_as_unique_ident x in
                     (uu____5909, aq) in
                   FStar_Parser_AST.PatVar uu____5902 in
                 mk1 uu____5901 in
               let uu____5912 = FStar_Options.print_bound_var_types () in
               if uu____5912
               then
                 let uu____5915 =
                   let uu____5916 =
                     let uu____5917 =
                       let uu____5922 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5922) in
                     FStar_Parser_AST.PatAscribed uu____5917 in
                   mk1 uu____5916 in
                 FStar_Pervasives_Native.Some uu____5915
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
              (fun uu____6011  ->
                 match uu____6011 with
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
              (fun uu____6055  ->
                 match uu____6055 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____6062 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____6062
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____6072;
             FStar_Syntax_Syntax.fv_delta = uu____6073;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____6110 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____6110 FStar_List.rev in
          let args1 =
            let uu____6125 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6144  ->
                      match uu____6144 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____6125 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____6214 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6214
            | (hd1::tl1,hd2::tl2) ->
                let uu____6237 = map21 tl1 tl2 in (hd1, hd2) :: uu____6237 in
          let args2 =
            let uu____6255 = map21 fields1 args1 in
            FStar_All.pipe_right uu____6255 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____6307  ->
                 match uu____6307 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____6321 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____6321 with
           | FStar_Pervasives_Native.Some (op,uu____6329) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____6338 =
                 let uu____6339 =
                   let uu____6346 = bv_as_unique_ident v1 in
                   let uu____6347 = to_arg_qual imp_opt in
                   (uu____6346, uu____6347) in
                 FStar_Parser_AST.PatVar uu____6339 in
               mk1 uu____6338)
      | FStar_Syntax_Syntax.Pat_wild uu____6352 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____6364 =
              let uu____6365 =
                let uu____6372 = bv_as_unique_ident bv in
                (uu____6372,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____6365 in
            mk1 uu____6364 in
          let uu____6375 = FStar_Options.print_bound_var_types () in
          if uu____6375
          then
            let uu____6376 =
              let uu____6377 =
                let uu____6382 = resugar_term term in (pat, uu____6382) in
              FStar_Parser_AST.PatAscribed uu____6377 in
            mk1 uu____6376
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___193_6388  ->
    match uu___193_6388 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6397 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6398 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6399 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6404 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6413 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6422 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___194_6425  ->
    match uu___194_6425 with
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
          (tylid,uvs,bs,t,uu____6456,datacons) ->
          let uu____6466 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____6486,uu____6487,uu____6488,inductive_lid,uu____6490,uu____6491)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____6496 -> failwith "unexpected")) in
          (match uu____6466 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____6515 = FStar_Options.print_implicits () in
                 if uu____6515 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____6524 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___195_6527  ->
                           match uu___195_6527 with
                           | FStar_Syntax_Syntax.RecordType uu____6528 ->
                               true
                           | uu____6537 -> false)) in
                 if uu____6524
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____6585,univs1,term,uu____6588,num,uu____6590)
                         ->
                         let uu____6595 =
                           let uu____6596 = FStar_Syntax_Subst.compress term in
                           uu____6596.FStar_Syntax_Syntax.n in
                         (match uu____6595 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6612) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6672  ->
                                        match uu____6672 with
                                        | (b,qual) ->
                                            let uu____6687 =
                                              let uu____6688 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6688 in
                                            let uu____6689 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6687, uu____6689,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6700 -> failwith "unexpected")
                     | uu____6711 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6832,num,uu____6834) ->
                          let c =
                            let uu____6852 =
                              let uu____6855 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6855 in
                            ((l.FStar_Ident.ident), uu____6852,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6872 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6948 ->
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
        let uu____6966 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6966;
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
      let uu____6979 = ts in
      match uu____6979 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6987 =
            let uu____6988 =
              let uu____7001 =
                let uu____7010 =
                  let uu____7017 =
                    let uu____7018 =
                      let uu____7031 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____7031) in
                    FStar_Parser_AST.TyconAbbrev uu____7018 in
                  (uu____7017, FStar_Pervasives_Native.None) in
                [uu____7010] in
              (false, uu____7001) in
            FStar_Parser_AST.Tycon uu____6988 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6987
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
            let uu____7085 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____7085 with
            | (bs,action_defn) ->
                let uu____7092 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____7092 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____7100 = FStar_Options.print_implicits () in
                       if uu____7100
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____7105 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____7105 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____7118 =
                           let uu____7129 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____7129,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____7118 in
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
          let uu____7203 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____7203 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____7211 = FStar_Options.print_implicits () in
                if uu____7211 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____7216 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____7216 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7273) ->
        let uu____7282 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____7302 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____7319 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____7326 -> false
                  | uu____7341 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____7282 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____7373 se1 =
               match uu____7373 with
               | (datacon_ses1,tycons) ->
                   let uu____7399 = resugar_typ datacon_ses1 se1 in
                   (match uu____7399 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____7414 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____7414 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____7449 =
                         let uu____7450 =
                           let uu____7451 =
                             let uu____7464 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____7464) in
                           FStar_Parser_AST.Tycon uu____7451 in
                         decl'_to_decl se uu____7450 in
                       FStar_Pervasives_Native.Some uu____7449
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____7494,uu____7495,uu____7496,uu____7497,uu____7498)
                            ->
                            let uu____7503 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____7503
                        | uu____7506 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____7509 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____7515,attrs) ->
        let uu____7525 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_7528  ->
                  match uu___196_7528 with
                  | FStar_Syntax_Syntax.Projector (uu____7529,uu____7530) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7531 -> true
                  | uu____7532 -> false)) in
        if uu____7525
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____7563) ->
               let uu____7576 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____7576
           | uu____7583 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____7588 =
          let uu____7589 =
            let uu____7590 =
              let uu____7595 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____7595) in
            FStar_Parser_AST.Assume uu____7590 in
          decl'_to_decl se uu____7589 in
        FStar_Pervasives_Native.Some uu____7588
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____7597 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7597
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____7599 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7599
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____7608,t) ->
              let uu____7620 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7620
          | uu____7621 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7629,t) ->
              let uu____7641 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7641
          | uu____7642 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7666 -> failwith "Should not happen hopefully" in
        let uu____7675 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7675
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7685 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7685 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7695 = FStar_Options.print_implicits () in
               if uu____7695 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7703 =
               let uu____7704 =
                 let uu____7705 =
                   let uu____7718 =
                     let uu____7727 =
                       let uu____7734 =
                         let uu____7735 =
                           let uu____7748 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7748) in
                         FStar_Parser_AST.TyconAbbrev uu____7735 in
                       (uu____7734, FStar_Pervasives_Native.None) in
                     [uu____7727] in
                   (false, uu____7718) in
                 FStar_Parser_AST.Tycon uu____7705 in
               decl'_to_decl se uu____7704 in
             FStar_Pervasives_Native.Some uu____7703)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7776 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7776
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7780 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___197_7783  ->
                  match uu___197_7783 with
                  | FStar_Syntax_Syntax.Projector (uu____7784,uu____7785) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7786 -> true
                  | uu____7787 -> false)) in
        if uu____7780
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7792 =
               (let uu____7793 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7793) || (FStar_List.isEmpty uvs) in
             if uu____7792
             then resugar_term t
             else
               (let uu____7795 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7795 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7803 =
                      let uu____7804 =
                        let uu____7811 = resugar_term t1 in
                        (uu____7811, universes, true) in
                      FStar_Parser_AST.Labeled uu____7804 in
                    FStar_Parser_AST.mk_term uu____7803
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____7812 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7812)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7813 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7830 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7845 -> FStar_Pervasives_Native.None