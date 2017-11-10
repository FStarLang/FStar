open Prims
let doc_to_string: FStar_Pprint.document -> Prims.string =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
let parser_term_to_string: FStar_Parser_AST.term -> Prims.string =
  fun t  ->
    let uu____7 = FStar_Parser_ToDocument.term_to_document t in
    doc_to_string uu____7
let map_opt:
  'Auu____12 'Auu____13 .
    Prims.unit ->
      ('Auu____13 -> 'Auu____12 FStar_Pervasives_Native.option) ->
        'Auu____13 Prims.list -> 'Auu____12 Prims.list
  = fun uu____27  -> FStar_List.filter_map
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____32 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____32
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp:
  'Auu____36 .
    ('Auu____36,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____36,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___236_90  ->
            match uu___236_90 with
            | (uu____97,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____98)) -> false
            | uu____101 -> true))
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
      | uu____176 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____184 = FStar_Options.print_universes () in
    if uu____184
    then
      let uu____185 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____185 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____216 ->
          let uu____217 = universe_to_int (Prims.parse_int "0") u in
          (match uu____217 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____224 =
                      let uu____225 =
                        let uu____226 =
                          let uu____237 = FStar_Util.string_of_int n1 in
                          (uu____237, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____226 in
                      FStar_Parser_AST.Const uu____225 in
                    mk1 uu____224 r
                | uu____248 ->
                    let e1 =
                      let uu____250 =
                        let uu____251 =
                          let uu____252 =
                            let uu____263 = FStar_Util.string_of_int n1 in
                            (uu____263, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____252 in
                        FStar_Parser_AST.Const uu____251 in
                      mk1 uu____250 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____280 ->
               let t =
                 let uu____284 =
                   let uu____285 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____285 in
                 mk1 uu____284 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____291 =
                        let uu____292 =
                          let uu____299 = resugar_universe x r in
                          (acc, uu____299, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____292 in
                      mk1 uu____291 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____301 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____312 =
              let uu____317 =
                let uu____318 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____318 in
              (uu____317, r) in
            FStar_Ident.mk_ident uu____312 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___237_337 =
      match uu___237_337 with
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
      | uu____428 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____455 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____465 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____465 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____473 ->
               let op =
                 let uu____477 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____511) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____477 in
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
      let uu____697 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____697 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____745 ->
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
                (let uu____798 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____798
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____814 =
      let uu____815 = FStar_Syntax_Subst.compress t in
      uu____815.FStar_Syntax_Syntax.n in
    match uu____814 with
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
    | uu____877 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____885 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____889 -> true
    | uu____890 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____921 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____921 in
    let var a r =
      let uu____929 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____929 in
    let uu____930 =
      let uu____931 = FStar_Syntax_Subst.compress t in
      uu____931.FStar_Syntax_Syntax.n in
    match uu____930 with
    | FStar_Syntax_Syntax.Tm_delayed uu____934 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____961 = let uu____964 = bv_as_unique_ident x in [uu____964] in
          FStar_Ident.lid_of_ids uu____961 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____967 = let uu____970 = bv_as_unique_ident x in [uu____970] in
          FStar_Ident.lid_of_ids uu____967 in
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
          let uu____988 =
            let uu____989 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____989 in
          mk1 uu____988
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
             | uu____999 -> failwith "wrong projector format")
          else
            (let uu____1003 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1006 =
                    let uu____1007 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1007 in
                  let uu____1008 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1006 <> uu____1008) in
             if uu____1003
             then
               let uu____1009 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1009
             else
               (let uu____1011 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1011))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1018 = FStar_Options.print_universes () in
        if uu____1018
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1025 =
                   let uu____1026 =
                     let uu____1033 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1033, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1026 in
                 mk1 uu____1025) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1036 = FStar_Syntax_Syntax.is_teff t in
        if uu____1036
        then
          let uu____1037 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1037
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1040 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1040
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1041 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1041
         | uu____1042 ->
             let uu____1043 = FStar_Options.print_universes () in
             if uu____1043
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1061 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1061))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1064) ->
        let uu____1085 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1085 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1093 = FStar_Options.print_implicits () in
               if uu____1093 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1107  ->
                       match uu____1107 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1137 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1137 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1145 = FStar_Options.print_implicits () in
               if uu____1145 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1151 =
                 FStar_All.pipe_right xs2
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1151 FStar_List.rev in
             let rec aux body3 uu___238_1170 =
               match uu___238_1170 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1186 =
          let uu____1191 =
            let uu____1192 = FStar_Syntax_Syntax.mk_binder x in [uu____1192] in
          FStar_Syntax_Subst.open_term uu____1191 phi in
        (match uu____1186 with
         | (x1,phi1) ->
             let b =
               let uu____1196 =
                 let uu____1199 = FStar_List.hd x1 in
                 resugar_binder uu____1199 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1196 in
             let uu____1204 =
               let uu____1205 =
                 let uu____1210 = resugar_term phi1 in (b, uu____1210) in
               FStar_Parser_AST.Refine uu____1205 in
             mk1 uu____1204)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___239_1252 =
          match uu___239_1252 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1322 -> failwith "last of an empty list" in
        let rec last_two uu___240_1358 =
          match uu___240_1358 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1389::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1466::t1 -> last_two t1 in
        let rec last_three uu___241_1507 =
          match uu___241_1507 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1538::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1565::uu____1566::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1674::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1760  ->
                    match uu____1760 with
                    | (e2,qual) ->
                        let uu____1779 = resugar_term e2 in
                        (uu____1779, qual))) in
          let e2 = resugar_term e1 in
          let res_impl desugared_tm qual =
            let uu____1794 = resugar_imp qual in
            match uu____1794 with
            | FStar_Pervasives_Native.Some imp -> imp
            | FStar_Pervasives_Native.None  ->
                ((let uu____1799 =
                    let uu____1804 =
                      let uu____1805 = parser_term_to_string desugared_tm in
                      FStar_Util.format1
                        "Inaccessible argument %s in function application"
                        uu____1805 in
                    (FStar_Errors.InaccessibleArgument, uu____1804) in
                  FStar_Errors.maybe_fatal_error t.FStar_Syntax_Syntax.pos
                    uu____1799);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1818  ->
                 match uu____1818 with
                 | (x,qual) ->
                     let uu____1831 =
                       let uu____1832 =
                         let uu____1839 = res_impl x qual in
                         (acc, x, uu____1839) in
                       FStar_Parser_AST.App uu____1832 in
                     mk1 uu____1831) e2 args2 in
        let args1 =
          let uu____1849 = FStar_Options.print_implicits () in
          if uu____1849 then args else filter_imp args in
        let uu____1861 = resugar_term_as_op e in
        (match uu____1861 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1872) ->
             (match args1 with
              | (fst1,uu____1878)::(snd1,uu____1880)::rest ->
                  let e1 =
                    let uu____1911 =
                      let uu____1912 =
                        let uu____1919 =
                          let uu____1922 = resugar_term fst1 in
                          let uu____1923 =
                            let uu____1926 = resugar_term snd1 in
                            [uu____1926] in
                          uu____1922 :: uu____1923 in
                        ((FStar_Ident.id_of_text "*"), uu____1919) in
                      FStar_Parser_AST.Op uu____1912 in
                    mk1 uu____1911 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1939  ->
                         match uu____1939 with
                         | (x,uu____1945) ->
                             let uu____1946 =
                               let uu____1947 =
                                 let uu____1954 =
                                   let uu____1957 =
                                     let uu____1960 = resugar_term x in
                                     [uu____1960] in
                                   e1 :: uu____1957 in
                                 ((FStar_Ident.id_of_text "*"), uu____1954) in
                               FStar_Parser_AST.Op uu____1947 in
                             mk1 uu____1946) e1 rest
              | uu____1963 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1972) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1998)::[] -> b
               | uu____2015 -> failwith "wrong arguments to dtuple" in
             let uu____2026 =
               let uu____2027 = FStar_Syntax_Subst.compress body in
               uu____2027.FStar_Syntax_Syntax.n in
             (match uu____2026 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2032) ->
                  let uu____2053 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2053 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2061 = FStar_Options.print_implicits () in
                         if uu____2061 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2073 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2094  ->
                            match uu____2094 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2106) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2112) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2117 = FStar_List.hd args1 in
             (match uu____2117 with
              | (t1,uu____2131) ->
                  let uu____2136 =
                    let uu____2137 = FStar_Syntax_Subst.compress t1 in
                    uu____2137.FStar_Syntax_Syntax.n in
                  (match uu____2136 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2142 =
                         let uu____2143 =
                           let uu____2148 = resugar_term t1 in
                           (uu____2148, f) in
                         FStar_Parser_AST.Project uu____2143 in
                       mk1 uu____2142
                   | uu____2149 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2150) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2170 =
               match new_args with
               | (a1,uu____2188)::(a2,uu____2190)::[] -> (a1, a2)
               | uu____2221 -> failwith "wrong arguments to try_with" in
             (match uu____2170 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2252 =
                      let uu____2253 = FStar_Syntax_Subst.compress term in
                      uu____2253.FStar_Syntax_Syntax.n in
                    match uu____2252 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2258) ->
                        let uu____2279 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2279 with | (x1,e2) -> e2)
                    | uu____2286 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2288 = decomp body in resugar_term uu____2288 in
                  let handler1 =
                    let uu____2290 = decomp handler in
                    resugar_term uu____2290 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2296,uu____2297,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2329,uu____2330,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2351 =
                          let uu____2352 =
                            let uu____2361 = resugar_body t11 in
                            (uu____2361, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2352 in
                        mk1 uu____2351
                    | uu____2364 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2419 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2449) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2455) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2540 -> (xs, pat, t1) in
             let resugar body =
               let uu____2551 =
                 let uu____2552 = FStar_Syntax_Subst.compress body in
                 uu____2552.FStar_Syntax_Syntax.n in
               match uu____2551 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2557) ->
                   let uu____2578 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2578 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2586 = FStar_Options.print_implicits () in
                          if uu____2586 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2595 =
                          let uu____2604 =
                            let uu____2605 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2605.FStar_Syntax_Syntax.n in
                          match uu____2604 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2674  ->
                                                 match uu____2674 with
                                                 | (e2,uu____2680) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2683) ->
                                    let uu____2684 =
                                      let uu____2687 =
                                        let uu____2688 = name s r in
                                        mk1 uu____2688 in
                                      [uu____2687] in
                                    [uu____2684]
                                | uu____2693 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2702 ->
                              let uu____2703 = resugar_term body2 in
                              ([], uu____2703) in
                        (match uu____2595 with
                         | (pats,body3) ->
                             let uu____2720 = uncurry xs3 pats body3 in
                             (match uu____2720 with
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
               | uu____2768 ->
                   if op = "forall"
                   then
                     let uu____2769 =
                       let uu____2770 =
                         let uu____2783 = resugar_term body in
                         ([], [[]], uu____2783) in
                       FStar_Parser_AST.QForall uu____2770 in
                     mk1 uu____2769
                   else
                     (let uu____2795 =
                        let uu____2796 =
                          let uu____2809 = resugar_term body in
                          ([], [[]], uu____2809) in
                        FStar_Parser_AST.QExists uu____2796 in
                      mk1 uu____2795) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2836)::[] -> resugar b
                | uu____2853 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2863) ->
             let uu____2868 = FStar_List.hd args1 in
             (match uu____2868 with | (e1,uu____2882) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2927  ->
                       match uu____2927 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____2934 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2934 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2941 =
                         let uu____2942 =
                           let uu____2949 =
                             let uu____2952 = last1 args1 in
                             resugar uu____2952 in
                           (op1, uu____2949) in
                         FStar_Parser_AST.Op uu____2942 in
                       mk1 uu____2941
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2967 =
                         let uu____2968 =
                           let uu____2975 =
                             let uu____2978 = last_two args1 in
                             resugar uu____2978 in
                           (op1, uu____2975) in
                         FStar_Parser_AST.Op uu____2968 in
                       mk1 uu____2967
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2993 =
                         let uu____2994 =
                           let uu____3001 =
                             let uu____3004 = last_three args1 in
                             resugar uu____3004 in
                           (op1, uu____3001) in
                         FStar_Parser_AST.Op uu____2994 in
                       mk1 uu____2993
                   | uu____3013 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3020 =
                    let uu____3021 =
                      let uu____3028 =
                        let uu____3031 = last_two args1 in resugar uu____3031 in
                      (op1, uu____3028) in
                    FStar_Parser_AST.Op uu____3021 in
                  mk1 uu____3020
              | uu____3040 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3043,t1)::[]) ->
        let bnds =
          let uu____3116 =
            let uu____3121 = resugar_pat pat in
            let uu____3122 = resugar_term e in (uu____3121, uu____3122) in
          [uu____3116] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3140,t1)::(pat2,uu____3143,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3239 =
          let uu____3240 =
            let uu____3247 = resugar_term e in
            let uu____3248 = resugar_term t1 in
            let uu____3249 = resugar_term t2 in
            (uu____3247, uu____3248, uu____3249) in
          FStar_Parser_AST.If uu____3240 in
        mk1 uu____3239
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3307 =
          match uu____3307 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3338 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3338 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3342 =
          let uu____3343 =
            let uu____3358 = resugar_term e in
            let uu____3359 = FStar_List.map resugar_branch branches in
            (uu____3358, uu____3359) in
          FStar_Parser_AST.Match uu____3343 in
        mk1 uu____3342
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3399) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3466 =
          let uu____3467 =
            let uu____3476 = resugar_term e in (uu____3476, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3467 in
        mk1 uu____3466
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3500 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3500 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3525 =
                 let uu____3530 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3530 in
               match uu____3525 with
               | (univs1,td) ->
                   let uu____3541 =
                     let uu____3550 =
                       let uu____3551 = FStar_Syntax_Subst.compress td in
                       uu____3551.FStar_Syntax_Syntax.n in
                     match uu____3550 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3562,(t1,uu____3564)::(d,uu____3566)::[]) ->
                         (t1, d)
                     | uu____3609 -> failwith "wrong let binding format" in
                   (match uu____3541 with
                    | (typ,def) ->
                        let uu____3636 =
                          let uu____3643 =
                            let uu____3644 = FStar_Syntax_Subst.compress def in
                            uu____3644.FStar_Syntax_Syntax.n in
                          match uu____3643 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3655) ->
                              let uu____3676 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3676 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3690 =
                                       FStar_Options.print_implicits () in
                                     if uu____3690 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3692 -> ([], def, false) in
                        (match uu____3636 with
                         | (binders,term,is_pat_app) ->
                             let uu____3716 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3727 =
                                     let uu____3728 =
                                       let uu____3729 =
                                         let uu____3736 =
                                           bv_as_unique_ident bv in
                                         (uu____3736,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3729 in
                                     mk_pat uu____3728 in
                                   (uu____3727, term) in
                             (match uu____3716 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3772  ->
                                              match uu____3772 with
                                              | (bv,q) ->
                                                  let uu____3787 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3787
                                                    (fun q1  ->
                                                       let uu____3799 =
                                                         let uu____3800 =
                                                           let uu____3807 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3807, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3800 in
                                                       mk_pat uu____3799))) in
                                    let uu____3810 =
                                      let uu____3815 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3815) in
                                    let uu____3818 =
                                      universe_to_string univs1 in
                                    (uu____3810, uu____3818)
                                  else
                                    (let uu____3824 =
                                       let uu____3829 = resugar_term term1 in
                                       (pat, uu____3829) in
                                     let uu____3830 =
                                       universe_to_string univs1 in
                                     (uu____3824, uu____3830))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3876 =
                   let uu____3877 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3877 in
                 if uu____3876
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___242_3897  ->
                      match uu___242_3897 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3938) ->
        let s =
          let uu____3964 =
            let uu____3965 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3965 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____3964 in
        let uu____3966 = mk1 FStar_Parser_AST.Wild in label s uu____3966
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___243_3976 =
          match uu___243_3976 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____3997 =
                  let uu____3998 = FStar_Syntax_Subst.compress h in
                  uu____3998.FStar_Syntax_Syntax.n in
                match uu____3997 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4018 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4018, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4041 = head_fv_universes_args h1 in
                    (match uu____4041 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4129 = head_fv_universes_args head1 in
                    (match uu____4129 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4201 ->
                    let uu____4202 =
                      let uu____4207 =
                        let uu____4208 =
                          let uu____4209 = resugar_term h in
                          parser_term_to_string uu____4209 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4208 in
                      (FStar_Errors.NotApplicationOrFv, uu____4207) in
                    FStar_Errors.raise_error uu____4202
                      e.FStar_Syntax_Syntax.pos in
              let uu____4226 =
                try
                  let uu____4278 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4278
                with
                | FStar_Errors.Err uu____4299 ->
                    let uu____4304 =
                      let uu____4309 =
                        let uu____4310 =
                          let uu____4311 = resugar_term e in
                          parser_term_to_string uu____4311 in
                        FStar_Util.format1 "wrong Data_app head format %s"
                          uu____4310 in
                      (FStar_Errors.WrongDataAppHeadFormat, uu____4309) in
                    FStar_Errors.raise_error uu____4304
                      e.FStar_Syntax_Syntax.pos in
              (match uu____4226 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4365 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4365, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4389  ->
                          match uu____4389 with
                          | (t1,q) ->
                              let uu____4408 = resugar_imp q in
                              (match uu____4408 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4418 =
                                     let uu____4423 = resugar_term t1 in
                                     (uu____4423, rimp) in
                                   FStar_Pervasives_Native.Some uu____4418
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4439 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4441 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4441) in
                     if uu____4439
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4464,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4489 =
                      let uu____4490 =
                        let uu____4499 = resugar_seq t11 in
                        (uu____4499, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4490 in
                    mk1 uu____4489
                | uu____4502 -> t1 in
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
               | uu____4524 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4526 =
                let uu____4527 = FStar_Syntax_Subst.compress e in
                uu____4527.FStar_Syntax_Syntax.n in
              (match uu____4526 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4531;
                      FStar_Syntax_Syntax.vars = uu____4532;_},(term,uu____4534)::[])
                   -> resugar_term term
               | uu____4563 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4601  ->
                       match uu____4601 with
                       | (x,uu____4607) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4609,p) ->
             let uu____4611 =
               let uu____4612 =
                 let uu____4619 = resugar_term e in (uu____4619, l, p) in
               FStar_Parser_AST.Labeled uu____4612 in
             mk1 uu____4611
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4621,s,uu____4623) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4628 ->
                  (FStar_Errors.maybe_fatal_error e.FStar_Syntax_Syntax.pos
                     (FStar_Errors.MetaAlienNotATmUnknow,
                       "Meta_alien was not a Tm_unknown");
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4637 =
               let uu____4638 =
                 let uu____4647 = resugar_term e in
                 let uu____4648 =
                   let uu____4649 =
                     let uu____4650 =
                       let uu____4661 =
                         let uu____4668 =
                           let uu____4673 = resugar_term t1 in
                           (uu____4673, FStar_Parser_AST.Nothing) in
                         [uu____4668] in
                       (name1, uu____4661) in
                     FStar_Parser_AST.Construct uu____4650 in
                   mk1 uu____4649 in
                 (uu____4647, uu____4648, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4638 in
             mk1 uu____4637
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4691,t1) ->
             let uu____4697 =
               let uu____4698 =
                 let uu____4707 = resugar_term e in
                 let uu____4708 =
                   let uu____4709 =
                     let uu____4710 =
                       let uu____4721 =
                         let uu____4728 =
                           let uu____4733 = resugar_term t1 in
                           (uu____4733, FStar_Parser_AST.Nothing) in
                         [uu____4728] in
                       (name1, uu____4721) in
                     FStar_Parser_AST.Construct uu____4710 in
                   mk1 uu____4709 in
                 (uu____4707, uu____4708, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4698 in
             mk1 uu____4697)
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
             let uu____4781 = FStar_Options.print_universes () in
             if uu____4781
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
             let uu____4842 = FStar_Options.print_universes () in
             if uu____4842
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
          let uu____4883 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4883, FStar_Parser_AST.Nothing) in
        let uu____4884 = FStar_Options.print_effect_args () in
        if uu____4884
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
                    let uu____4971 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____4971, (FStar_Pervasives_Native.snd post)) in
                  let uu____4980 =
                    let uu____4989 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____4989 then [] else [pre] in
                  let uu____5019 =
                    let uu____5028 =
                      let uu____5037 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5037 then [] else [pats] in
                    FStar_List.append [post1] uu____5028 in
                  FStar_List.append uu____4980 uu____5019
              | uu____5091 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5120  ->
                 match uu____5120 with
                 | (e,uu____5130) ->
                     let uu____5131 = resugar_term e in
                     (uu____5131, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___244_5152 =
            match uu___244_5152 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5185 = resugar_term e in
                       (uu____5185, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5190 -> aux l tl1) in
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
      let uu____5235 = b in
      match uu____5235 with
      | (x,aq) ->
          let uu____5240 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5240
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5254 =
                     let uu____5255 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5255 in
                   FStar_Parser_AST.mk_binder uu____5254 r
                     FStar_Parser_AST.Type_level imp
               | uu____5256 ->
                   let uu____5257 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5257
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5259 =
                        let uu____5260 =
                          let uu____5265 = bv_as_unique_ident x in
                          (uu____5265, e) in
                        FStar_Parser_AST.Annotated uu____5260 in
                      FStar_Parser_AST.mk_binder uu____5259 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5274 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5274 in
      let uu____5275 =
        let uu____5276 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5276.FStar_Syntax_Syntax.n in
      match uu____5275 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5284 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5284
          else
            (let uu____5286 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5286
               (fun aq  ->
                  let uu____5298 =
                    let uu____5299 =
                      let uu____5300 =
                        let uu____5307 = bv_as_unique_ident x in
                        (uu____5307, aq) in
                      FStar_Parser_AST.PatVar uu____5300 in
                    mk1 uu____5299 in
                  FStar_Pervasives_Native.Some uu____5298))
      | uu____5310 ->
          let uu____5311 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5311
            (fun aq  ->
               let pat =
                 let uu____5326 =
                   let uu____5327 =
                     let uu____5334 = bv_as_unique_ident x in
                     (uu____5334, aq) in
                   FStar_Parser_AST.PatVar uu____5327 in
                 mk1 uu____5326 in
               let uu____5337 = FStar_Options.print_bound_var_types () in
               if uu____5337
               then
                 let uu____5340 =
                   let uu____5341 =
                     let uu____5342 =
                       let uu____5347 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5347) in
                     FStar_Parser_AST.PatAscribed uu____5342 in
                   mk1 uu____5341 in
                 FStar_Pervasives_Native.Some uu____5340
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
              (fun uu____5424  ->
                 match uu____5424 with
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
              (fun uu____5459  ->
                 match uu____5459 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5466 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5466
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5472;
             FStar_Syntax_Syntax.fv_delta = uu____5473;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5500 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5500 FStar_List.rev in
          let args1 =
            let uu____5516 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5536  ->
                      match uu____5536 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5516 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5606 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5606
            | (hd1::tl1,hd2::tl2) ->
                let uu____5629 = map21 tl1 tl2 in (hd1, hd2) :: uu____5629 in
          let args2 =
            let uu____5647 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5647 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5698  ->
                 match uu____5698 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5708 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5708 with
           | FStar_Pervasives_Native.Some (op,uu____5716) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5725 =
                 let uu____5726 =
                   let uu____5733 = bv_as_unique_ident v1 in
                   let uu____5734 = to_arg_qual imp_opt in
                   (uu____5733, uu____5734) in
                 FStar_Parser_AST.PatVar uu____5726 in
               mk1 uu____5725)
      | FStar_Syntax_Syntax.Pat_wild uu____5739 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5747 =
              let uu____5748 =
                let uu____5755 = bv_as_unique_ident bv in
                (uu____5755,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5748 in
            mk1 uu____5747 in
          let uu____5758 = FStar_Options.print_bound_var_types () in
          if uu____5758
          then
            let uu____5759 =
              let uu____5760 =
                let uu____5765 = resugar_term term in (pat, uu____5765) in
              FStar_Parser_AST.PatAscribed uu____5760 in
            mk1 uu____5759
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___245_5771  ->
    match uu___245_5771 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5780 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5781 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5782 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5787 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5796 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5805 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___246_5808  ->
    match uu___246_5808 with
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
          (tylid,uvs,bs,t,uu____5835,datacons) ->
          let uu____5845 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5872,uu____5873,uu____5874,inductive_lid,uu____5876,uu____5877)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5882 -> failwith "unexpected")) in
          (match uu____5845 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5901 = FStar_Options.print_implicits () in
                 if uu____5901 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5911 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___247_5916  ->
                           match uu___247_5916 with
                           | FStar_Syntax_Syntax.RecordType uu____5917 ->
                               true
                           | uu____5926 -> false)) in
                 if uu____5911
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5974,univs1,term,uu____5977,num,uu____5979)
                         ->
                         let uu____5984 =
                           let uu____5985 = FStar_Syntax_Subst.compress term in
                           uu____5985.FStar_Syntax_Syntax.n in
                         (match uu____5984 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5999) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6060  ->
                                        match uu____6060 with
                                        | (b,qual) ->
                                            let uu____6075 =
                                              let uu____6076 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6076 in
                                            let uu____6077 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6075, uu____6077,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6088 -> failwith "unexpected")
                     | uu____6099 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6220,num,uu____6222) ->
                          let c =
                            let uu____6240 =
                              let uu____6243 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6243 in
                            ((l.FStar_Ident.ident), uu____6240,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6260 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6336 ->
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
        let uu____6354 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6354;
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
      let uu____6367 = ts in
      match uu____6367 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6375 =
            let uu____6376 =
              let uu____6389 =
                let uu____6398 =
                  let uu____6405 =
                    let uu____6406 =
                      let uu____6419 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6419) in
                    FStar_Parser_AST.TyconAbbrev uu____6406 in
                  (uu____6405, FStar_Pervasives_Native.None) in
                [uu____6398] in
              (false, uu____6389) in
            FStar_Parser_AST.Tycon uu____6376 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6375
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
            let uu____6473 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6473 with
            | (bs,action_defn) ->
                let uu____6480 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6480 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6488 = FStar_Options.print_implicits () in
                       if uu____6488
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6493 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6493 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6507 =
                           let uu____6518 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6518,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6507 in
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
          let uu____6592 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6592 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6600 = FStar_Options.print_implicits () in
                if uu____6600 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6605 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6605 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6662) ->
        let uu____6671 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6693 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6710 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6717 -> false
                  | uu____6732 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6671 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6764 se1 =
               match uu____6764 with
               | (datacon_ses1,tycons) ->
                   let uu____6790 = resugar_typ datacon_ses1 se1 in
                   (match uu____6790 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6805 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6805 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6840 =
                         let uu____6841 =
                           let uu____6842 =
                             let uu____6855 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6855) in
                           FStar_Parser_AST.Tycon uu____6842 in
                         decl'_to_decl se uu____6841 in
                       FStar_Pervasives_Native.Some uu____6840
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6886,uu____6887,uu____6888,uu____6889,uu____6890)
                            ->
                            let uu____6895 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6895
                        | uu____6898 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6901 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6907) ->
        let uu____6912 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___248_6918  ->
                  match uu___248_6918 with
                  | FStar_Syntax_Syntax.Projector (uu____6919,uu____6920) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6921 -> true
                  | uu____6922 -> false)) in
        if uu____6912
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6945) ->
               let uu____6958 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6958
           | uu____6965 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6969,fml) ->
        let uu____6971 =
          let uu____6972 =
            let uu____6973 =
              let uu____6978 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6978) in
            FStar_Parser_AST.Assume uu____6973 in
          decl'_to_decl se uu____6972 in
        FStar_Pervasives_Native.Some uu____6971
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6980 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6980
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6982 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6982
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6991,t) ->
              let uu____7003 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7003
          | uu____7004 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7012,t) ->
              let uu____7024 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7024
          | uu____7025 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7049 -> failwith "Should not happen hopefully" in
        let uu____7058 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7058
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
        let uu____7068 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7068 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7078 = FStar_Options.print_implicits () in
               if uu____7078 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7087 =
               let uu____7088 =
                 let uu____7089 =
                   let uu____7102 =
                     let uu____7111 =
                       let uu____7118 =
                         let uu____7119 =
                           let uu____7132 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7132) in
                         FStar_Parser_AST.TyconAbbrev uu____7119 in
                       (uu____7118, FStar_Pervasives_Native.None) in
                     [uu____7111] in
                   (false, uu____7102) in
                 FStar_Parser_AST.Tycon uu____7089 in
               decl'_to_decl se uu____7088 in
             FStar_Pervasives_Native.Some uu____7087)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7160 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7160
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7164 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___249_7170  ->
                  match uu___249_7170 with
                  | FStar_Syntax_Syntax.Projector (uu____7171,uu____7172) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7173 -> true
                  | uu____7174 -> false)) in
        if uu____7164
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7179 =
               (let uu____7182 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7182) || (FStar_List.isEmpty uvs) in
             if uu____7179
             then resugar_term t
             else
               (let uu____7184 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7184 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7192 = resugar_term t1 in
                    label universes uu____7192) in
           let uu____7193 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7193)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7194 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7211 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7226 -> FStar_Pervasives_Native.None