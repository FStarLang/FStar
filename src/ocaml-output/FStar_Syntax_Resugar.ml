open Prims
let doc_to_string: FStar_Pprint.document -> Prims.string =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
let parser_term_to_string: FStar_Parser_AST.term -> Prims.string =
  fun t  ->
    let uu____9 = FStar_Parser_ToDocument.term_to_document t in
    doc_to_string uu____9
let map_opt:
  'Auu____18 'Auu____19 .
    Prims.unit ->
      ('Auu____19 -> 'Auu____18 FStar_Pervasives_Native.option) ->
        'Auu____19 Prims.list -> 'Auu____18 Prims.list
  = fun uu____33  -> FStar_List.filter_map
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____39 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____39
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp:
  'Auu____45 .
    ('Auu____45,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____45,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___193_99  ->
            match uu___193_99 with
            | (uu____106,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____107)) -> false
            | uu____110 -> true))
let label: Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
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
    FStar_Parser_AST.imp FStar_Pervasives_Native.option
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Hash
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        FStar_Pervasives_Native.None
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
      | uu____191 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____200 = FStar_Options.print_universes () in
    if uu____200
    then
      let uu____201 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____201 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____234 ->
          let uu____235 = universe_to_int (Prims.parse_int "0") u in
          (match uu____235 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____242 =
                      let uu____243 =
                        let uu____244 =
                          let uu____255 = FStar_Util.string_of_int n1 in
                          (uu____255, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____244 in
                      FStar_Parser_AST.Const uu____243 in
                    mk1 uu____242 r
                | uu____266 ->
                    let e1 =
                      let uu____268 =
                        let uu____269 =
                          let uu____270 =
                            let uu____281 = FStar_Util.string_of_int n1 in
                            (uu____281, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____270 in
                        FStar_Parser_AST.Const uu____269 in
                      mk1 uu____268 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____298 ->
               let t =
                 let uu____302 =
                   let uu____303 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____303 in
                 mk1 uu____302 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____309 =
                        let uu____310 =
                          let uu____317 = resugar_universe x r in
                          (acc, uu____317, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____310 in
                      mk1 uu____309 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____319 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____330 =
              let uu____335 =
                let uu____336 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____336 in
              (uu____335, r) in
            FStar_Ident.mk_ident uu____330 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___194_356 =
      match uu___194_356 with
      | "Amp" -> FStar_Pervasives_Native.Some ("&", (Prims.parse_int "0"))
      | "At" -> FStar_Pervasives_Native.Some ("@", (Prims.parse_int "0"))
      | "Plus" -> FStar_Pervasives_Native.Some ("+", (Prims.parse_int "0"))
      | "Minus" -> FStar_Pervasives_Native.Some ("-", (Prims.parse_int "0"))
      | "Subtraction" ->
          FStar_Pervasives_Native.Some ("-", (Prims.parse_int "2"))
      | "Tilde" -> FStar_Pervasives_Native.Some ("~", (Prims.parse_int "0"))
      | "Slash" -> FStar_Pervasives_Native.Some ("/", (Prims.parse_int "0"))
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", (Prims.parse_int "0"))
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
      | "Dollar" -> FStar_Pervasives_Native.Some ("$", (Prims.parse_int "0"))
      | "Dot" -> FStar_Pervasives_Native.Some (".", (Prims.parse_int "0"))
      | uu____447 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____474 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____484 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____484 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____492 ->
               let op =
                 let uu____496 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____530) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____496 in
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
      let uu____717 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____717 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____765 ->
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
                (let uu____818 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____818
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____834 =
      let uu____835 = FStar_Syntax_Subst.compress t in
      uu____835.FStar_Syntax_Syntax.n in
    match uu____834 with
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
        let uu____858 = string_to_op s in
        (match uu____858 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____884 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____897 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____906 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____911 -> true
    | uu____912 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____943 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____943 in
    let var a r =
      let uu____951 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____951 in
    let uu____952 =
      let uu____953 = FStar_Syntax_Subst.compress t in
      uu____953.FStar_Syntax_Syntax.n in
    match uu____952 with
    | FStar_Syntax_Syntax.Tm_delayed uu____956 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____983 = let uu____986 = bv_as_unique_ident x in [uu____986] in
          FStar_Ident.lid_of_ids uu____983 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____989 = let uu____992 = bv_as_unique_ident x in [uu____992] in
          FStar_Ident.lid_of_ids uu____989 in
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
          let uu____1010 =
            let uu____1011 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____1011 in
          mk1 uu____1010
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
             | uu____1021 -> failwith "wrong projector format")
          else
            (let uu____1025 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1028 =
                    let uu____1029 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1029 in
                  let uu____1030 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1028 <> uu____1030) in
             if uu____1025
             then
               let uu____1031 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1031
             else
               (let uu____1033 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1033))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1040 = FStar_Options.print_universes () in
        if uu____1040
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
        let uu____1107 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1107 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1115 = FStar_Options.print_implicits () in
               if uu____1115 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1129  ->
                       match uu____1129 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1159 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1159 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1167 = FStar_Options.print_implicits () in
               if uu____1167 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1173 =
                 FStar_All.pipe_right xs2
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1173 FStar_List.rev in
             let rec aux body3 uu___195_1192 =
               match uu___195_1192 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1208 =
          let uu____1213 =
            let uu____1214 = FStar_Syntax_Syntax.mk_binder x in [uu____1214] in
          FStar_Syntax_Subst.open_term uu____1213 phi in
        (match uu____1208 with
         | (x1,phi1) ->
             let b =
               let uu____1218 =
                 let uu____1221 = FStar_List.hd x1 in
                 resugar_binder uu____1221 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1218 in
             let uu____1226 =
               let uu____1227 =
                 let uu____1232 = resugar_term phi1 in (b, uu____1232) in
               FStar_Parser_AST.Refine uu____1227 in
             mk1 uu____1226)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___196_1274 =
          match uu___196_1274 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1344 -> failwith "last of an empty list" in
        let rec last_two uu___197_1380 =
          match uu___197_1380 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1411::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1488::t1 -> last_two t1 in
        let rec last_three uu___198_1529 =
          match uu___198_1529 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1560::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1587::uu____1588::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1696::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1782  ->
                    match uu____1782 with
                    | (e2,qual) ->
                        let uu____1801 = resugar_term e2 in
                        (uu____1801, qual))) in
          let e2 = resugar_term e1 in
          let res_impl desugared_tm qual =
            let uu____1816 = resugar_imp qual in
            match uu____1816 with
            | FStar_Pervasives_Native.Some imp -> imp
            | FStar_Pervasives_Native.None  ->
                ((let uu____1821 =
                    let uu____1822 = parser_term_to_string desugared_tm in
                    FStar_Util.format1
                      "Inaccessible argument %s in function application"
                      uu____1822 in
                  FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1821);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1835  ->
                 match uu____1835 with
                 | (x,qual) ->
                     let uu____1848 =
                       let uu____1849 =
                         let uu____1856 = res_impl x qual in
                         (acc, x, uu____1856) in
                       FStar_Parser_AST.App uu____1849 in
                     mk1 uu____1848) e2 args2 in
        let args1 =
          let uu____1866 = FStar_Options.print_implicits () in
          if uu____1866 then args else filter_imp args in
        let uu____1878 = resugar_term_as_op e in
        (match uu____1878 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1889) ->
             (match args1 with
              | (fst1,uu____1895)::(snd1,uu____1897)::rest ->
                  let e1 =
                    let uu____1928 =
                      let uu____1929 =
                        let uu____1936 =
                          let uu____1939 = resugar_term fst1 in
                          let uu____1940 =
                            let uu____1943 = resugar_term snd1 in
                            [uu____1943] in
                          uu____1939 :: uu____1940 in
                        ((FStar_Ident.id_of_text "*"), uu____1936) in
                      FStar_Parser_AST.Op uu____1929 in
                    mk1 uu____1928 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1956  ->
                         match uu____1956 with
                         | (x,uu____1962) ->
                             let uu____1963 =
                               let uu____1964 =
                                 let uu____1971 =
                                   let uu____1974 =
                                     let uu____1977 = resugar_term x in
                                     [uu____1977] in
                                   e1 :: uu____1974 in
                                 ((FStar_Ident.id_of_text "*"), uu____1971) in
                               FStar_Parser_AST.Op uu____1964 in
                             mk1 uu____1963) e1 rest
              | uu____1980 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1989) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2015)::[] -> b
               | uu____2032 -> failwith "wrong arguments to dtuple" in
             let uu____2043 =
               let uu____2044 = FStar_Syntax_Subst.compress body in
               uu____2044.FStar_Syntax_Syntax.n in
             (match uu____2043 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2049) ->
                  let uu____2070 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2070 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2078 = FStar_Options.print_implicits () in
                         if uu____2078 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2090 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2111  ->
                            match uu____2111 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2123) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2129) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2134 = FStar_List.hd args1 in
             (match uu____2134 with
              | (t1,uu____2148) ->
                  let uu____2153 =
                    let uu____2154 = FStar_Syntax_Subst.compress t1 in
                    uu____2154.FStar_Syntax_Syntax.n in
                  (match uu____2153 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2159 =
                         let uu____2160 =
                           let uu____2165 = resugar_term t1 in
                           (uu____2165, f) in
                         FStar_Parser_AST.Project uu____2160 in
                       mk1 uu____2159
                   | uu____2166 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2167) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2187 =
               match new_args with
               | (a1,uu____2205)::(a2,uu____2207)::[] -> (a1, a2)
               | uu____2238 -> failwith "wrong arguments to try_with" in
             (match uu____2187 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2269 =
                      let uu____2270 = FStar_Syntax_Subst.compress term in
                      uu____2270.FStar_Syntax_Syntax.n in
                    match uu____2269 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2275) ->
                        let uu____2296 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2296 with | (x1,e2) -> e2)
                    | uu____2303 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2305 = decomp body in resugar_term uu____2305 in
                  let handler1 =
                    let uu____2307 = decomp handler in
                    resugar_term uu____2307 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2313,uu____2314,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2346,uu____2347,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2368 =
                          let uu____2369 =
                            let uu____2378 = resugar_body t11 in
                            (uu____2378, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2369 in
                        mk1 uu____2368
                    | uu____2381 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2436 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2466) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2472) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2557 -> (xs, pat, t1) in
             let resugar body =
               let uu____2568 =
                 let uu____2569 = FStar_Syntax_Subst.compress body in
                 uu____2569.FStar_Syntax_Syntax.n in
               match uu____2568 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2574) ->
                   let uu____2595 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2595 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2603 = FStar_Options.print_implicits () in
                          if uu____2603 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2612 =
                          let uu____2621 =
                            let uu____2622 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2622.FStar_Syntax_Syntax.n in
                          match uu____2621 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2691  ->
                                                 match uu____2691 with
                                                 | (e2,uu____2697) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2700) ->
                                    let uu____2701 =
                                      let uu____2704 =
                                        let uu____2705 = name s r in
                                        mk1 uu____2705 in
                                      [uu____2704] in
                                    [uu____2701]
                                | uu____2710 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2719 ->
                              let uu____2720 = resugar_term body2 in
                              ([], uu____2720) in
                        (match uu____2612 with
                         | (pats,body3) ->
                             let uu____2737 = uncurry xs3 pats body3 in
                             (match uu____2737 with
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
               | uu____2785 ->
                   if op = "forall"
                   then
                     let uu____2786 =
                       let uu____2787 =
                         let uu____2800 = resugar_term body in
                         ([], [[]], uu____2800) in
                       FStar_Parser_AST.QForall uu____2787 in
                     mk1 uu____2786
                   else
                     (let uu____2812 =
                        let uu____2813 =
                          let uu____2826 = resugar_term body in
                          ([], [[]], uu____2826) in
                        FStar_Parser_AST.QExists uu____2813 in
                      mk1 uu____2812) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2853)::[] -> resugar b
                | uu____2870 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2880) ->
             let uu____2885 = FStar_List.hd args1 in
             (match uu____2885 with | (e1,uu____2899) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2944  ->
                       match uu____2944 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_40 when _0_40 = (Prims.parse_int "0") ->
                  let uu____2951 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2951 with
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2958 =
                         let uu____2959 =
                           let uu____2966 =
                             let uu____2969 = last1 args1 in
                             resugar uu____2969 in
                           (op1, uu____2966) in
                         FStar_Parser_AST.Op uu____2959 in
                       mk1 uu____2958
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2984 =
                         let uu____2985 =
                           let uu____2992 =
                             let uu____2995 = last_two args1 in
                             resugar uu____2995 in
                           (op1, uu____2992) in
                         FStar_Parser_AST.Op uu____2985 in
                       mk1 uu____2984
                   | _0_43 when
                       (_0_43 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3010 =
                         let uu____3011 =
                           let uu____3018 =
                             let uu____3021 = last_three args1 in
                             resugar uu____3021 in
                           (op1, uu____3018) in
                         FStar_Parser_AST.Op uu____3011 in
                       mk1 uu____3010
                   | uu____3030 -> resugar_as_app e args1)
              | _0_44 when
                  (_0_44 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3037 =
                    let uu____3038 =
                      let uu____3045 =
                        let uu____3048 = last_two args1 in resugar uu____3048 in
                      (op1, uu____3045) in
                    FStar_Parser_AST.Op uu____3038 in
                  mk1 uu____3037
              | uu____3057 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3060,t1)::[]) ->
        let bnds =
          let uu____3133 =
            let uu____3138 = resugar_pat pat in
            let uu____3139 = resugar_term e in (uu____3138, uu____3139) in
          [uu____3133] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3157,t1)::(pat2,uu____3160,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3256 =
          let uu____3257 =
            let uu____3264 = resugar_term e in
            let uu____3265 = resugar_term t1 in
            let uu____3266 = resugar_term t2 in
            (uu____3264, uu____3265, uu____3266) in
          FStar_Parser_AST.If uu____3257 in
        mk1 uu____3256
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3324 =
          match uu____3324 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3355 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3355 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3359 =
          let uu____3360 =
            let uu____3375 = resugar_term e in
            let uu____3376 = FStar_List.map resugar_branch branches in
            (uu____3375, uu____3376) in
          FStar_Parser_AST.Match uu____3360 in
        mk1 uu____3359
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3416) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3483 =
          let uu____3484 =
            let uu____3493 = resugar_term e in (uu____3493, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3484 in
        mk1 uu____3483
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3517 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3517 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3542 =
                 let uu____3547 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3547 in
               match uu____3542 with
               | (univs1,td) ->
                   let uu____3558 =
                     let uu____3567 =
                       let uu____3568 = FStar_Syntax_Subst.compress td in
                       uu____3568.FStar_Syntax_Syntax.n in
                     match uu____3567 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3579,(t1,uu____3581)::(d,uu____3583)::[]) ->
                         (t1, d)
                     | uu____3626 -> failwith "wrong let binding format" in
                   (match uu____3558 with
                    | (typ,def) ->
                        let uu____3653 =
                          let uu____3660 =
                            let uu____3661 = FStar_Syntax_Subst.compress def in
                            uu____3661.FStar_Syntax_Syntax.n in
                          match uu____3660 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3672) ->
                              let uu____3693 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3693 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3707 =
                                       FStar_Options.print_implicits () in
                                     if uu____3707 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3709 -> ([], def, false) in
                        (match uu____3653 with
                         | (binders,term,is_pat_app) ->
                             let uu____3733 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3744 =
                                     let uu____3745 =
                                       let uu____3746 =
                                         let uu____3753 =
                                           bv_as_unique_ident bv in
                                         (uu____3753,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3746 in
                                     mk_pat uu____3745 in
                                   (uu____3744, term) in
                             (match uu____3733 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3789  ->
                                              match uu____3789 with
                                              | (bv,q) ->
                                                  let uu____3804 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3804
                                                    (fun q1  ->
                                                       let uu____3816 =
                                                         let uu____3817 =
                                                           let uu____3824 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3824, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3817 in
                                                       mk_pat uu____3816))) in
                                    let uu____3827 =
                                      let uu____3832 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3832) in
                                    let uu____3835 =
                                      universe_to_string univs1 in
                                    (uu____3827, uu____3835)
                                  else
                                    (let uu____3841 =
                                       let uu____3846 = resugar_term term1 in
                                       (pat, uu____3846) in
                                     let uu____3847 =
                                       universe_to_string univs1 in
                                     (uu____3841, uu____3847))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3893 =
                   let uu____3894 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3894 in
                 if uu____3893
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___199_3914  ->
                      match uu___199_3914 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3955) ->
        let s =
          let uu____3981 =
            let uu____3982 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3982 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____3981 in
        let uu____3983 = mk1 FStar_Parser_AST.Wild in label s uu____3983
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___200_3993 =
          match uu___200_3993 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4014 =
                  let uu____4015 = FStar_Syntax_Subst.compress h in
                  uu____4015.FStar_Syntax_Syntax.n in
                match uu____4014 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4035 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4035, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4058 = head_fv_universes_args h1 in
                    (match uu____4058 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4146 = head_fv_universes_args head1 in
                    (match uu____4146 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4218 ->
                    let uu____4219 =
                      let uu____4220 =
                        let uu____4221 =
                          let uu____4222 = resugar_term h in
                          parser_term_to_string uu____4222 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4221 in
                      FStar_Errors.Err uu____4220 in
                    FStar_Exn.raise uu____4219 in
              let uu____4239 =
                try
                  let uu____4291 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4291
                with
                | FStar_Errors.Err uu____4312 ->
                    let uu____4313 =
                      let uu____4314 =
                        let uu____4319 =
                          let uu____4320 =
                            let uu____4321 = resugar_term e in
                            parser_term_to_string uu____4321 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4320 in
                        (uu____4319, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4314 in
                    FStar_Exn.raise uu____4313 in
              (match uu____4239 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4375 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4375, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4399  ->
                          match uu____4399 with
                          | (t1,q) ->
                              let uu____4418 = resugar_imp q in
                              (match uu____4418 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4428 =
                                     let uu____4433 = resugar_term t1 in
                                     (uu____4433, rimp) in
                                   FStar_Pervasives_Native.Some uu____4428
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4449 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4451 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4451) in
                     if uu____4449
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4474,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4499 =
                      let uu____4500 =
                        let uu____4509 = resugar_seq t11 in
                        (uu____4509, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4500 in
                    mk1 uu____4499
                | uu____4512 -> t1 in
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
               | uu____4534 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4536 =
                let uu____4537 = FStar_Syntax_Subst.compress e in
                uu____4537.FStar_Syntax_Syntax.n in
              (match uu____4536 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4541;
                      FStar_Syntax_Syntax.vars = uu____4542;_},(term,uu____4544)::[])
                   -> resugar_term term
               | uu____4573 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4611  ->
                       match uu____4611 with
                       | (x,uu____4617) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4619,p) ->
             let uu____4621 =
               let uu____4622 =
                 let uu____4629 = resugar_term e in (uu____4629, l, p) in
               FStar_Parser_AST.Labeled uu____4622 in
             mk1 uu____4621
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4631,s,uu____4633) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4638 ->
                  (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                     "Meta_alien was not a Tm_unknown";
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4647 =
               let uu____4648 =
                 let uu____4657 = resugar_term e in
                 let uu____4658 =
                   let uu____4659 =
                     let uu____4660 =
                       let uu____4671 =
                         let uu____4678 =
                           let uu____4683 = resugar_term t1 in
                           (uu____4683, FStar_Parser_AST.Nothing) in
                         [uu____4678] in
                       (name1, uu____4671) in
                     FStar_Parser_AST.Construct uu____4660 in
                   mk1 uu____4659 in
                 (uu____4657, uu____4658, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4648 in
             mk1 uu____4647
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4701,t1) ->
             let uu____4707 =
               let uu____4708 =
                 let uu____4717 = resugar_term e in
                 let uu____4718 =
                   let uu____4719 =
                     let uu____4720 =
                       let uu____4731 =
                         let uu____4738 =
                           let uu____4743 = resugar_term t1 in
                           (uu____4743, FStar_Parser_AST.Nothing) in
                         [uu____4738] in
                       (name1, uu____4731) in
                     FStar_Parser_AST.Construct uu____4720 in
                   mk1 uu____4719 in
                 (uu____4717, uu____4718, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4708 in
             mk1 uu____4707)
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
             let uu____4791 = FStar_Options.print_universes () in
             if uu____4791
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
             let uu____4852 = FStar_Options.print_universes () in
             if uu____4852
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
          let uu____4893 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4893, FStar_Parser_AST.Nothing) in
        let uu____4894 = FStar_Options.print_effect_args () in
        if uu____4894
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              match c1.FStar_Syntax_Syntax.effect_args with
              | pre::post::pats::[] ->
                  let post1 =
                    let uu____4981 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____4981, (FStar_Pervasives_Native.snd post)) in
                  let uu____4990 =
                    let uu____4999 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____4999 then [] else [pre] in
                  let uu____5029 =
                    let uu____5038 =
                      let uu____5047 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5047 then [] else [pats] in
                    FStar_List.append [post1] uu____5038 in
                  FStar_List.append uu____4990 uu____5029
              | uu____5101 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5130  ->
                 match uu____5130 with
                 | (e,uu____5140) ->
                     let uu____5141 = resugar_term e in
                     (uu____5141, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___201_5162 =
            match uu___201_5162 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5195 = resugar_term e in
                       (uu____5195, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5200 -> aux l tl1) in
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
      let uu____5245 = b in
      match uu____5245 with
      | (x,aq) ->
          let uu____5250 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5250
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5264 =
                     let uu____5265 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5265 in
                   FStar_Parser_AST.mk_binder uu____5264 r
                     FStar_Parser_AST.Type_level imp
               | uu____5266 ->
                   let uu____5267 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5267
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5269 =
                        let uu____5270 =
                          let uu____5275 = bv_as_unique_ident x in
                          (uu____5275, e) in
                        FStar_Parser_AST.Annotated uu____5270 in
                      FStar_Parser_AST.mk_binder uu____5269 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5284 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5284 in
      let uu____5285 =
        let uu____5286 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5286.FStar_Syntax_Syntax.n in
      match uu____5285 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5294 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5294
          else
            (let uu____5296 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5296
               (fun aq  ->
                  let uu____5308 =
                    let uu____5309 =
                      let uu____5310 =
                        let uu____5317 = bv_as_unique_ident x in
                        (uu____5317, aq) in
                      FStar_Parser_AST.PatVar uu____5310 in
                    mk1 uu____5309 in
                  FStar_Pervasives_Native.Some uu____5308))
      | uu____5320 ->
          let uu____5321 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5321
            (fun aq  ->
               let pat =
                 let uu____5336 =
                   let uu____5337 =
                     let uu____5344 = bv_as_unique_ident x in
                     (uu____5344, aq) in
                   FStar_Parser_AST.PatVar uu____5337 in
                 mk1 uu____5336 in
               let uu____5347 = FStar_Options.print_bound_var_types () in
               if uu____5347
               then
                 let uu____5350 =
                   let uu____5351 =
                     let uu____5352 =
                       let uu____5357 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5357) in
                     FStar_Parser_AST.PatAscribed uu____5352 in
                   mk1 uu____5351 in
                 FStar_Pervasives_Native.Some uu____5350
               else FStar_Pervasives_Native.Some pat)
and resugar_pat: FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
    let to_arg_qual bopt =
      FStar_Util.bind_opt bopt
        (fun b  ->
           if b
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
              (fun uu____5434  ->
                 match uu____5434 with
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
              (fun uu____5469  ->
                 match uu____5469 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5476 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5476
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5482;
             FStar_Syntax_Syntax.fv_delta = uu____5483;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5510 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5510 FStar_List.rev in
          let args1 =
            let uu____5526 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5546  ->
                      match uu____5546 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5526 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5616 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5616
            | (hd1::tl1,hd2::tl2) ->
                let uu____5639 = map21 tl1 tl2 in (hd1, hd2) :: uu____5639 in
          let args2 =
            let uu____5657 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5657 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5708  ->
                 match uu____5708 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5718 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5718 with
           | FStar_Pervasives_Native.Some (op,uu____5726) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5735 =
                 let uu____5736 =
                   let uu____5743 = bv_as_unique_ident v1 in
                   let uu____5744 = to_arg_qual imp_opt in
                   (uu____5743, uu____5744) in
                 FStar_Parser_AST.PatVar uu____5736 in
               mk1 uu____5735)
      | FStar_Syntax_Syntax.Pat_wild uu____5749 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5757 =
              let uu____5758 =
                let uu____5765 = bv_as_unique_ident bv in
                (uu____5765,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5758 in
            mk1 uu____5757 in
          let uu____5768 = FStar_Options.print_bound_var_types () in
          if uu____5768
          then
            let uu____5769 =
              let uu____5770 =
                let uu____5775 = resugar_term term in (pat, uu____5775) in
              FStar_Parser_AST.PatAscribed uu____5770 in
            mk1 uu____5769
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___202_5782  ->
    match uu___202_5782 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5791 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5792 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5793 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5798 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5807 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5816 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___203_5820  ->
    match uu___203_5820 with
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
          (tylid,uvs,bs,t,uu____5849,datacons) ->
          let uu____5859 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5886,uu____5887,uu____5888,inductive_lid,uu____5890,uu____5891)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5896 -> failwith "unexpected")) in
          (match uu____5859 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5915 = FStar_Options.print_implicits () in
                 if uu____5915 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5925 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___204_5930  ->
                           match uu___204_5930 with
                           | FStar_Syntax_Syntax.RecordType uu____5931 ->
                               true
                           | uu____5940 -> false)) in
                 if uu____5925
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5988,univs1,term,uu____5991,num,uu____5993)
                         ->
                         let uu____5998 =
                           let uu____5999 = FStar_Syntax_Subst.compress term in
                           uu____5999.FStar_Syntax_Syntax.n in
                         (match uu____5998 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6013) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6074  ->
                                        match uu____6074 with
                                        | (b,qual) ->
                                            let uu____6089 =
                                              let uu____6090 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6090 in
                                            let uu____6091 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6089, uu____6091,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6102 -> failwith "unexpected")
                     | uu____6113 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6234,num,uu____6236) ->
                          let c =
                            let uu____6254 =
                              let uu____6257 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6257 in
                            ((l.FStar_Ident.ident), uu____6254,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6274 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6350 ->
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
        let uu____6371 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6371;
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
      let uu____6388 = ts in
      match uu____6388 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6396 =
            let uu____6397 =
              let uu____6410 =
                let uu____6419 =
                  let uu____6426 =
                    let uu____6427 =
                      let uu____6440 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6440) in
                    FStar_Parser_AST.TyconAbbrev uu____6427 in
                  (uu____6426, FStar_Pervasives_Native.None) in
                [uu____6419] in
              (false, uu____6410) in
            FStar_Parser_AST.Tycon uu____6397 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6396
let resugar_tscheme: FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun ts  -> resugar_tscheme' "tscheme" ts
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
            let uu____6499 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6499 with
            | (bs,action_defn) ->
                let uu____6506 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6506 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6514 = FStar_Options.print_implicits () in
                       if uu____6514
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6519 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6519 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6533 =
                           let uu____6544 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6544,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6533 in
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
          let uu____6618 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6618 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6626 = FStar_Options.print_implicits () in
                if uu____6626 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6631 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6631 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6689) ->
        let uu____6698 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6720 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6737 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6744 -> false
                  | uu____6759 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6698 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6791 se1 =
               match uu____6791 with
               | (datacon_ses1,tycons) ->
                   let uu____6817 = resugar_typ datacon_ses1 se1 in
                   (match uu____6817 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6832 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6832 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6867 =
                         let uu____6868 =
                           let uu____6869 =
                             let uu____6882 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6882) in
                           FStar_Parser_AST.Tycon uu____6869 in
                         decl'_to_decl se uu____6868 in
                       FStar_Pervasives_Native.Some uu____6867
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6913,uu____6914,uu____6915,uu____6916,uu____6917)
                            ->
                            let uu____6922 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6922
                        | uu____6925 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6928 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6934) ->
        let uu____6939 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___205_6945  ->
                  match uu___205_6945 with
                  | FStar_Syntax_Syntax.Projector (uu____6946,uu____6947) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6948 -> true
                  | uu____6949 -> false)) in
        if uu____6939
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6972) ->
               let uu____6985 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6985
           | uu____6992 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6996,fml) ->
        let uu____6998 =
          let uu____6999 =
            let uu____7000 =
              let uu____7005 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____7005) in
            FStar_Parser_AST.Assume uu____7000 in
          decl'_to_decl se uu____6999 in
        FStar_Pervasives_Native.Some uu____6998
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____7007 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7007
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____7009 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7009
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____7018,t) ->
              let uu____7030 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7030
          | uu____7031 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7039,t) ->
              let uu____7051 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7051
          | uu____7052 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7076 -> failwith "Should not happen hopefully" in
        let uu____7085 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7085
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7095 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7095 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7105 = FStar_Options.print_implicits () in
               if uu____7105 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7114 =
               let uu____7115 =
                 let uu____7116 =
                   let uu____7129 =
                     let uu____7138 =
                       let uu____7145 =
                         let uu____7146 =
                           let uu____7159 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7159) in
                         FStar_Parser_AST.TyconAbbrev uu____7146 in
                       (uu____7145, FStar_Pervasives_Native.None) in
                     [uu____7138] in
                   (false, uu____7129) in
                 FStar_Parser_AST.Tycon uu____7116 in
               decl'_to_decl se uu____7115 in
             FStar_Pervasives_Native.Some uu____7114)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7187 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7187
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7191 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___206_7197  ->
                  match uu___206_7197 with
                  | FStar_Syntax_Syntax.Projector (uu____7198,uu____7199) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7200 -> true
                  | uu____7201 -> false)) in
        if uu____7191
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7206 =
               (let uu____7209 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7209) || (FStar_List.isEmpty uvs) in
             if uu____7206
             then resugar_term t
             else
               (let uu____7211 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7211 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7219 = resugar_term t1 in
                    label universes uu____7219) in
           let uu____7220 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7220)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7221 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7238 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7253 -> FStar_Pervasives_Native.None