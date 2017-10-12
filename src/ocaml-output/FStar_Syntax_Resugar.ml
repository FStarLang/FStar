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
         (fun uu___185_99  ->
            match uu___185_99 with
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
          let id1 =
            let uu____330 =
              let uu____335 =
                let uu____336 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____336 in
              (uu____335, r) in
            FStar_Ident.mk_ident uu____330 in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___186_356 =
      match uu___186_356 with
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
                  let uu____1039 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1028 <> uu____1039) in
             if uu____1025
             then
               let uu____1052 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1052
             else
               (let uu____1054 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1054))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1061 = FStar_Options.print_universes () in
        if uu____1061
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1068 =
                   let uu____1069 =
                     let uu____1076 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1076, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1069 in
                 mk1 uu____1068) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1079 = FStar_Syntax_Syntax.is_teff t in
        if uu____1079
        then
          let uu____1080 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1080
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1083 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1083
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1084 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1084
         | uu____1085 ->
             let uu____1086 = FStar_Options.print_universes () in
             if uu____1086
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1104 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1104))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1107) ->
        let uu____1128 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1128 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1136 = FStar_Options.print_implicits () in
               if uu____1136 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1150  ->
                       match uu____1150 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1180 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1180 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1188 = FStar_Options.print_implicits () in
               if uu____1188 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1194 =
                 FStar_All.pipe_right xs2
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1194 FStar_List.rev in
             let rec aux body3 uu___187_1213 =
               match uu___187_1213 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1229 =
          let uu____1234 =
            let uu____1235 = FStar_Syntax_Syntax.mk_binder x in [uu____1235] in
          FStar_Syntax_Subst.open_term uu____1234 phi in
        (match uu____1229 with
         | (x1,phi1) ->
             let b =
               let uu____1239 =
                 let uu____1242 = FStar_List.hd x1 in
                 resugar_binder uu____1242 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1239 in
             let uu____1247 =
               let uu____1248 =
                 let uu____1253 = resugar_term phi1 in (b, uu____1253) in
               FStar_Parser_AST.Refine uu____1248 in
             mk1 uu____1247)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___188_1295 =
          match uu___188_1295 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1365 -> failwith "last of an empty list" in
        let rec last_two uu___189_1401 =
          match uu___189_1401 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1432::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1509::t1 -> last_two t1 in
        let rec last_three uu___190_1550 =
          match uu___190_1550 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1581::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1608::uu____1609::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1717::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1803  ->
                    match uu____1803 with
                    | (e2,qual) ->
                        let uu____1822 = resugar_term e2 in
                        (uu____1822, qual))) in
          let e2 = resugar_term e1 in
          let res_impl desugared_tm qual =
            let uu____1837 = resugar_imp qual in
            match uu____1837 with
            | FStar_Pervasives_Native.Some imp -> imp
            | FStar_Pervasives_Native.None  ->
                ((let uu____1842 =
                    let uu____1843 = parser_term_to_string desugared_tm in
                    FStar_Util.format1
                      "Inaccessible argument %s in function application"
                      uu____1843 in
                  FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1842);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1856  ->
                 match uu____1856 with
                 | (x,qual) ->
                     let uu____1869 =
                       let uu____1870 =
                         let uu____1877 = res_impl x qual in
                         (acc, x, uu____1877) in
                       FStar_Parser_AST.App uu____1870 in
                     mk1 uu____1869) e2 args2 in
        let args1 =
          let uu____1887 = FStar_Options.print_implicits () in
          if uu____1887 then args else filter_imp args in
        let uu____1899 = resugar_term_as_op e in
        (match uu____1899 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1910) ->
             (match args1 with
              | (fst1,uu____1916)::(snd1,uu____1918)::rest ->
                  let e1 =
                    let uu____1949 =
                      let uu____1950 =
                        let uu____1957 =
                          let uu____1960 = resugar_term fst1 in
                          let uu____1961 =
                            let uu____1964 = resugar_term snd1 in
                            [uu____1964] in
                          uu____1960 :: uu____1961 in
                        ((FStar_Ident.id_of_text "*"), uu____1957) in
                      FStar_Parser_AST.Op uu____1950 in
                    mk1 uu____1949 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1977  ->
                         match uu____1977 with
                         | (x,uu____1983) ->
                             let uu____1984 =
                               let uu____1985 =
                                 let uu____1992 =
                                   let uu____1995 =
                                     let uu____1998 = resugar_term x in
                                     [uu____1998] in
                                   e1 :: uu____1995 in
                                 ((FStar_Ident.id_of_text "*"), uu____1992) in
                               FStar_Parser_AST.Op uu____1985 in
                             mk1 uu____1984) e1 rest
              | uu____2001 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2010) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2036)::[] -> b
               | uu____2053 -> failwith "wrong arguments to dtuple" in
             let uu____2064 =
               let uu____2065 = FStar_Syntax_Subst.compress body in
               uu____2065.FStar_Syntax_Syntax.n in
             (match uu____2064 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2070) ->
                  let uu____2091 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2091 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2099 = FStar_Options.print_implicits () in
                         if uu____2099 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2111 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2132  ->
                            match uu____2132 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2144) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2150) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2155 = FStar_List.hd args1 in
             (match uu____2155 with
              | (t1,uu____2169) ->
                  let uu____2174 =
                    let uu____2175 = FStar_Syntax_Subst.compress t1 in
                    uu____2175.FStar_Syntax_Syntax.n in
                  (match uu____2174 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2180 =
                         let uu____2181 =
                           let uu____2186 = resugar_term t1 in
                           (uu____2186, f) in
                         FStar_Parser_AST.Project uu____2181 in
                       mk1 uu____2180
                   | uu____2187 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2188) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2208 =
               match new_args with
               | (a1,uu____2226)::(a2,uu____2228)::[] -> (a1, a2)
               | uu____2259 -> failwith "wrong arguments to try_with" in
             (match uu____2208 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2290 =
                      let uu____2291 = FStar_Syntax_Subst.compress term in
                      uu____2291.FStar_Syntax_Syntax.n in
                    match uu____2290 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2296) ->
                        let uu____2317 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2317 with | (x1,e2) -> e2)
                    | uu____2324 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2326 = decomp body in resugar_term uu____2326 in
                  let handler1 =
                    let uu____2328 = decomp handler in
                    resugar_term uu____2328 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2334,uu____2335,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2367,uu____2368,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2389 =
                          let uu____2390 =
                            let uu____2399 = resugar_body t11 in
                            (uu____2399, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2390 in
                        mk1 uu____2389
                    | uu____2402 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2457 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2487) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2493) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2578 -> (xs, pat, t1) in
             let resugar body =
               let uu____2589 =
                 let uu____2590 = FStar_Syntax_Subst.compress body in
                 uu____2590.FStar_Syntax_Syntax.n in
               match uu____2589 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2595) ->
                   let uu____2616 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2616 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2624 = FStar_Options.print_implicits () in
                          if uu____2624 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2633 =
                          let uu____2642 =
                            let uu____2643 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2643.FStar_Syntax_Syntax.n in
                          match uu____2642 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2712  ->
                                                 match uu____2712 with
                                                 | (e2,uu____2718) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2721) ->
                                    let uu____2722 =
                                      let uu____2725 =
                                        let uu____2726 = name s r in
                                        mk1 uu____2726 in
                                      [uu____2725] in
                                    [uu____2722]
                                | uu____2731 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2740 ->
                              let uu____2741 = resugar_term body2 in
                              ([], uu____2741) in
                        (match uu____2633 with
                         | (pats,body3) ->
                             let uu____2758 = uncurry xs3 pats body3 in
                             (match uu____2758 with
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
               | uu____2806 ->
                   if op = "forall"
                   then
                     let uu____2807 =
                       let uu____2808 =
                         let uu____2821 = resugar_term body in
                         ([], [[]], uu____2821) in
                       FStar_Parser_AST.QForall uu____2808 in
                     mk1 uu____2807
                   else
                     (let uu____2833 =
                        let uu____2834 =
                          let uu____2847 = resugar_term body in
                          ([], [[]], uu____2847) in
                        FStar_Parser_AST.QExists uu____2834 in
                      mk1 uu____2833) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2874)::[] -> resugar b
                | uu____2891 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2901) ->
             let uu____2906 = FStar_List.hd args1 in
             (match uu____2906 with | (e1,uu____2920) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2965  ->
                       match uu____2965 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_40 when _0_40 = (Prims.parse_int "0") ->
                  let uu____2972 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2972 with
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2979 =
                         let uu____2980 =
                           let uu____2987 =
                             let uu____2990 = last1 args1 in
                             resugar uu____2990 in
                           (op1, uu____2987) in
                         FStar_Parser_AST.Op uu____2980 in
                       mk1 uu____2979
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____3005 =
                         let uu____3006 =
                           let uu____3013 =
                             let uu____3016 = last_two args1 in
                             resugar uu____3016 in
                           (op1, uu____3013) in
                         FStar_Parser_AST.Op uu____3006 in
                       mk1 uu____3005
                   | _0_43 when
                       (_0_43 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3031 =
                         let uu____3032 =
                           let uu____3039 =
                             let uu____3042 = last_three args1 in
                             resugar uu____3042 in
                           (op1, uu____3039) in
                         FStar_Parser_AST.Op uu____3032 in
                       mk1 uu____3031
                   | uu____3051 -> resugar_as_app e args1)
              | _0_44 when
                  (_0_44 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3058 =
                    let uu____3059 =
                      let uu____3066 =
                        let uu____3069 = last_two args1 in resugar uu____3069 in
                      (op1, uu____3066) in
                    FStar_Parser_AST.Op uu____3059 in
                  mk1 uu____3058
              | uu____3078 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3081,t1)::[]) ->
        let bnds =
          let uu____3154 =
            let uu____3159 = resugar_pat pat in
            let uu____3160 = resugar_term e in (uu____3159, uu____3160) in
          [uu____3154] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3178,t1)::(pat2,uu____3181,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3277 =
          let uu____3278 =
            let uu____3285 = resugar_term e in
            let uu____3286 = resugar_term t1 in
            let uu____3287 = resugar_term t2 in
            (uu____3285, uu____3286, uu____3287) in
          FStar_Parser_AST.If uu____3278 in
        mk1 uu____3277
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3345 =
          match uu____3345 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3376 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3376 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3380 =
          let uu____3381 =
            let uu____3396 = resugar_term e in
            let uu____3397 = FStar_List.map resugar_branch branches in
            (uu____3396, uu____3397) in
          FStar_Parser_AST.Match uu____3381 in
        mk1 uu____3380
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3437) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3504 =
          let uu____3505 =
            let uu____3514 = resugar_term e in (uu____3514, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3505 in
        mk1 uu____3504
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3538 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3538 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3563 =
                 let uu____3568 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3568 in
               match uu____3563 with
               | (univs1,td) ->
                   let uu____3579 =
                     let uu____3588 =
                       let uu____3589 = FStar_Syntax_Subst.compress td in
                       uu____3589.FStar_Syntax_Syntax.n in
                     match uu____3588 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3600,(t1,uu____3602)::(d,uu____3604)::[]) ->
                         (t1, d)
                     | uu____3647 -> failwith "wrong let binding format" in
                   (match uu____3579 with
                    | (typ,def) ->
                        let uu____3674 =
                          let uu____3681 =
                            let uu____3682 = FStar_Syntax_Subst.compress def in
                            uu____3682.FStar_Syntax_Syntax.n in
                          match uu____3681 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3693) ->
                              let uu____3714 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3714 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3728 =
                                       FStar_Options.print_implicits () in
                                     if uu____3728 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3730 -> ([], def, false) in
                        (match uu____3674 with
                         | (binders,term,is_pat_app) ->
                             let uu____3754 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3765 =
                                     let uu____3766 =
                                       let uu____3767 =
                                         let uu____3774 =
                                           bv_as_unique_ident bv in
                                         (uu____3774,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3767 in
                                     mk_pat uu____3766 in
                                   (uu____3765, term) in
                             (match uu____3754 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3810  ->
                                              match uu____3810 with
                                              | (bv,q) ->
                                                  let uu____3825 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3825
                                                    (fun q1  ->
                                                       let uu____3837 =
                                                         let uu____3838 =
                                                           let uu____3845 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3845, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3838 in
                                                       mk_pat uu____3837))) in
                                    let uu____3848 =
                                      let uu____3853 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3853) in
                                    let uu____3856 =
                                      universe_to_string univs1 in
                                    (uu____3848, uu____3856)
                                  else
                                    (let uu____3862 =
                                       let uu____3867 = resugar_term term1 in
                                       (pat, uu____3867) in
                                     let uu____3868 =
                                       universe_to_string univs1 in
                                     (uu____3862, uu____3868))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3914 =
                   let uu____3915 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3915 in
                 if uu____3914
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___191_3935  ->
                      match uu___191_3935 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3976) ->
        let s =
          let uu____4002 =
            let uu____4003 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____4003 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____4002 in
        let uu____4004 = mk1 FStar_Parser_AST.Wild in label s uu____4004
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___192_4014 =
          match uu___192_4014 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4035 =
                  let uu____4036 = FStar_Syntax_Subst.compress h in
                  uu____4036.FStar_Syntax_Syntax.n in
                match uu____4035 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4056 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4056, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4079 = head_fv_universes_args h1 in
                    (match uu____4079 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4167 = head_fv_universes_args head1 in
                    (match uu____4167 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4239 ->
                    let uu____4240 =
                      let uu____4241 =
                        let uu____4242 =
                          let uu____4243 = resugar_term h in
                          parser_term_to_string uu____4243 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4242 in
                      FStar_Errors.Err uu____4241 in
                    FStar_Exn.raise uu____4240 in
              let uu____4260 =
                try
                  let uu____4312 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4312
                with
                | FStar_Errors.Err uu____4333 ->
                    let uu____4334 =
                      let uu____4335 =
                        let uu____4340 =
                          let uu____4341 =
                            let uu____4342 = resugar_term e in
                            parser_term_to_string uu____4342 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4341 in
                        (uu____4340, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4335 in
                    FStar_Exn.raise uu____4334 in
              (match uu____4260 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4396 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4396, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4420  ->
                          match uu____4420 with
                          | (t1,q) ->
                              let uu____4439 = resugar_imp q in
                              (match uu____4439 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4449 =
                                     let uu____4454 = resugar_term t1 in
                                     (uu____4454, rimp) in
                                   FStar_Pervasives_Native.Some uu____4449
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4470 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4472 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4472) in
                     if uu____4470
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4495,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4520 =
                      let uu____4521 =
                        let uu____4530 = resugar_seq t11 in
                        (uu____4530, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4521 in
                    mk1 uu____4520
                | uu____4533 -> t1 in
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
               | uu____4555 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4557 =
                let uu____4558 = FStar_Syntax_Subst.compress e in
                uu____4558.FStar_Syntax_Syntax.n in
              (match uu____4557 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4562;
                      FStar_Syntax_Syntax.vars = uu____4563;_},(term,uu____4565)::[])
                   -> resugar_term term
               | uu____4594 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4632  ->
                       match uu____4632 with
                       | (x,uu____4638) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4640,p) ->
             let uu____4642 =
               let uu____4643 =
                 let uu____4650 = resugar_term e in (uu____4650, l, p) in
               FStar_Parser_AST.Labeled uu____4643 in
             mk1 uu____4642
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4652,s,uu____4654) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4659 ->
                  (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                     "Meta_alien was not a Tm_unknown";
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4668 =
               let uu____4669 =
                 let uu____4678 = resugar_term e in
                 let uu____4679 =
                   let uu____4680 =
                     let uu____4681 =
                       let uu____4692 =
                         let uu____4699 =
                           let uu____4704 = resugar_term t1 in
                           (uu____4704, FStar_Parser_AST.Nothing) in
                         [uu____4699] in
                       (name1, uu____4692) in
                     FStar_Parser_AST.Construct uu____4681 in
                   mk1 uu____4680 in
                 (uu____4678, uu____4679, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4669 in
             mk1 uu____4668
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4722,t1) ->
             let uu____4728 =
               let uu____4729 =
                 let uu____4738 = resugar_term e in
                 let uu____4739 =
                   let uu____4740 =
                     let uu____4741 =
                       let uu____4752 =
                         let uu____4759 =
                           let uu____4764 = resugar_term t1 in
                           (uu____4764, FStar_Parser_AST.Nothing) in
                         [uu____4759] in
                       (name1, uu____4752) in
                     FStar_Parser_AST.Construct uu____4741 in
                   mk1 uu____4740 in
                 (uu____4738, uu____4739, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4729 in
             mk1 uu____4728)
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
             let uu____4812 = FStar_Options.print_universes () in
             if uu____4812
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
             let uu____4873 = FStar_Options.print_universes () in
             if uu____4873
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
          let uu____4914 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4914, FStar_Parser_AST.Nothing) in
        let uu____4915 = FStar_Options.print_effect_args () in
        if uu____4915
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
                  let uu____4995 =
                    let uu____5004 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____5004 then [] else [pre] in
                  let uu____5034 =
                    let uu____5043 =
                      let uu____5052 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5052 then [] else [pats] in
                    FStar_List.append [post] uu____5043 in
                  FStar_List.append uu____4995 uu____5034
              | uu____5106 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5135  ->
                 match uu____5135 with
                 | (e,uu____5145) ->
                     let uu____5146 = resugar_term e in
                     (uu____5146, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___193_5167 =
            match uu___193_5167 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5200 = resugar_term e in
                       (uu____5200, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5205 -> aux l tl1) in
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
      let uu____5250 = b in
      match uu____5250 with
      | (x,aq) ->
          let uu____5255 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5255
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5269 =
                     let uu____5270 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5270 in
                   FStar_Parser_AST.mk_binder uu____5269 r
                     FStar_Parser_AST.Type_level imp
               | uu____5271 ->
                   let uu____5272 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5272
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5274 =
                        let uu____5275 =
                          let uu____5280 = bv_as_unique_ident x in
                          (uu____5280, e) in
                        FStar_Parser_AST.Annotated uu____5275 in
                      FStar_Parser_AST.mk_binder uu____5274 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5289 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5289 in
      let uu____5290 =
        let uu____5291 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5291.FStar_Syntax_Syntax.n in
      match uu____5290 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5299 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5299
          else
            (let uu____5301 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5301
               (fun aq  ->
                  let uu____5313 =
                    let uu____5314 =
                      let uu____5315 =
                        let uu____5322 = bv_as_unique_ident x in
                        (uu____5322, aq) in
                      FStar_Parser_AST.PatVar uu____5315 in
                    mk1 uu____5314 in
                  FStar_Pervasives_Native.Some uu____5313))
      | uu____5325 ->
          let uu____5326 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5326
            (fun aq  ->
               let pat =
                 let uu____5341 =
                   let uu____5342 =
                     let uu____5349 = bv_as_unique_ident x in
                     (uu____5349, aq) in
                   FStar_Parser_AST.PatVar uu____5342 in
                 mk1 uu____5341 in
               let uu____5352 = FStar_Options.print_bound_var_types () in
               if uu____5352
               then
                 let uu____5355 =
                   let uu____5356 =
                     let uu____5357 =
                       let uu____5362 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5362) in
                     FStar_Parser_AST.PatAscribed uu____5357 in
                   mk1 uu____5356 in
                 FStar_Pervasives_Native.Some uu____5355
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
              (fun uu____5439  ->
                 match uu____5439 with
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
              (fun uu____5474  ->
                 match uu____5474 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5481 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5481
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5487;
             FStar_Syntax_Syntax.fv_delta = uu____5488;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5515 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5515 FStar_List.rev in
          let args1 =
            let uu____5531 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5551  ->
                      match uu____5551 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5531 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5621 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5621
            | (hd1::tl1,hd2::tl2) ->
                let uu____5644 = map21 tl1 tl2 in (hd1, hd2) :: uu____5644 in
          let args2 =
            let uu____5662 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5662 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5713  ->
                 match uu____5713 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5723 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5723 with
           | FStar_Pervasives_Native.Some (op,uu____5731) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5740 =
                 let uu____5741 =
                   let uu____5748 = bv_as_unique_ident v1 in
                   let uu____5749 = to_arg_qual imp_opt in
                   (uu____5748, uu____5749) in
                 FStar_Parser_AST.PatVar uu____5741 in
               mk1 uu____5740)
      | FStar_Syntax_Syntax.Pat_wild uu____5754 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5762 =
              let uu____5763 =
                let uu____5770 = bv_as_unique_ident bv in
                (uu____5770,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5763 in
            mk1 uu____5762 in
          let uu____5773 = FStar_Options.print_bound_var_types () in
          if uu____5773
          then
            let uu____5774 =
              let uu____5775 =
                let uu____5780 = resugar_term term in (pat, uu____5780) in
              FStar_Parser_AST.PatAscribed uu____5775 in
            mk1 uu____5774
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___194_5787  ->
    match uu___194_5787 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5796 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5797 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5798 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5803 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5812 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5821 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___195_5825  ->
    match uu___195_5825 with
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
          (tylid,uvs,bs,t,uu____5854,datacons) ->
          let uu____5864 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5891,uu____5892,uu____5893,inductive_lid,uu____5895,uu____5896)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5901 -> failwith "unexpected")) in
          (match uu____5864 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5920 = FStar_Options.print_implicits () in
                 if uu____5920 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5930 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___196_5935  ->
                           match uu___196_5935 with
                           | FStar_Syntax_Syntax.RecordType uu____5936 ->
                               true
                           | uu____5945 -> false)) in
                 if uu____5930
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5993,univs1,term,uu____5996,num,uu____5998)
                         ->
                         let uu____6003 =
                           let uu____6004 = FStar_Syntax_Subst.compress term in
                           uu____6004.FStar_Syntax_Syntax.n in
                         (match uu____6003 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6018) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6079  ->
                                        match uu____6079 with
                                        | (b,qual) ->
                                            let uu____6094 =
                                              let uu____6095 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6095 in
                                            let uu____6096 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6094, uu____6096,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6107 -> failwith "unexpected")
                     | uu____6118 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6239,num,uu____6241) ->
                          let c =
                            let uu____6259 =
                              let uu____6262 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6262 in
                            ((l.FStar_Ident.ident), uu____6259,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6279 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6355 ->
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
        let uu____6376 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6376;
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
      let uu____6393 = ts in
      match uu____6393 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6401 =
            let uu____6402 =
              let uu____6415 =
                let uu____6424 =
                  let uu____6431 =
                    let uu____6432 =
                      let uu____6445 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6445) in
                    FStar_Parser_AST.TyconAbbrev uu____6432 in
                  (uu____6431, FStar_Pervasives_Native.None) in
                [uu____6424] in
              (false, uu____6415) in
            FStar_Parser_AST.Tycon uu____6402 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6401
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
            let uu____6504 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6504 with
            | (bs,action_defn) ->
                let uu____6511 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6511 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6519 = FStar_Options.print_implicits () in
                       if uu____6519
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6524 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6524 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6538 =
                           let uu____6549 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6549,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6538 in
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
          let uu____6623 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6623 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6631 = FStar_Options.print_implicits () in
                if uu____6631 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6636 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6636 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6694) ->
        let uu____6703 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6725 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6742 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6749 -> false
                  | uu____6764 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6703 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6796 se1 =
               match uu____6796 with
               | (datacon_ses1,tycons) ->
                   let uu____6822 = resugar_typ datacon_ses1 se1 in
                   (match uu____6822 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6837 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6837 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6872 =
                         let uu____6873 =
                           let uu____6874 =
                             let uu____6887 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6887) in
                           FStar_Parser_AST.Tycon uu____6874 in
                         decl'_to_decl se uu____6873 in
                       FStar_Pervasives_Native.Some uu____6872
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6918,uu____6919,uu____6920,uu____6921,uu____6922)
                            ->
                            let uu____6927 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6927
                        | uu____6930 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6933 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6939) ->
        let uu____6944 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___197_6950  ->
                  match uu___197_6950 with
                  | FStar_Syntax_Syntax.Projector (uu____6951,uu____6952) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6953 -> true
                  | uu____6954 -> false)) in
        if uu____6944
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6977) ->
               let uu____6990 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6990
           | uu____6997 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____7001,fml) ->
        let uu____7003 =
          let uu____7004 =
            let uu____7005 =
              let uu____7010 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____7010) in
            FStar_Parser_AST.Assume uu____7005 in
          decl'_to_decl se uu____7004 in
        FStar_Pervasives_Native.Some uu____7003
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____7012 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7012
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____7014 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7014
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____7023,t) ->
              let uu____7035 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7035
          | uu____7036 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7044,t) ->
              let uu____7056 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7056
          | uu____7057 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7081 -> failwith "Should not happen hopefully" in
        let uu____7090 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7090
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7100 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7100 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7110 = FStar_Options.print_implicits () in
               if uu____7110 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7119 =
               let uu____7120 =
                 let uu____7121 =
                   let uu____7134 =
                     let uu____7143 =
                       let uu____7150 =
                         let uu____7151 =
                           let uu____7164 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7164) in
                         FStar_Parser_AST.TyconAbbrev uu____7151 in
                       (uu____7150, FStar_Pervasives_Native.None) in
                     [uu____7143] in
                   (false, uu____7134) in
                 FStar_Parser_AST.Tycon uu____7121 in
               decl'_to_decl se uu____7120 in
             FStar_Pervasives_Native.Some uu____7119)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7192 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7192
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7196 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___198_7202  ->
                  match uu___198_7202 with
                  | FStar_Syntax_Syntax.Projector (uu____7203,uu____7204) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7205 -> true
                  | uu____7206 -> false)) in
        if uu____7196
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7211 =
               (let uu____7214 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7214) || (FStar_List.isEmpty uvs) in
             if uu____7211
             then resugar_term t
             else
               (let uu____7216 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7216 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7224 = resugar_term t1 in
                    label universes uu____7224) in
           let uu____7225 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7225)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7226 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7243 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7258 -> FStar_Pervasives_Native.None