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
         (fun uu___234_90  ->
            match uu___234_90 with
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
          let id1 =
            let uu____312 =
              let uu____317 =
                let uu____318 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____318 in
              (uu____317, r) in
            FStar_Ident.mk_ident uu____312 in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___235_337 =
      match uu___235_337 with
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
                  let uu____1017 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1006 <> uu____1017) in
             if uu____1003
             then
               let uu____1030 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1030
             else
               (let uu____1032 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1032))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1039 = FStar_Options.print_universes () in
        if uu____1039
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1046 =
                   let uu____1047 =
                     let uu____1054 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1054, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1047 in
                 mk1 uu____1046) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1057 = FStar_Syntax_Syntax.is_teff t in
        if uu____1057
        then
          let uu____1058 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1058
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1061 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1061
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1062 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1062
         | uu____1063 ->
             let uu____1064 = FStar_Options.print_universes () in
             if uu____1064
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1082 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1082))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1085) ->
        let uu____1106 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1106 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1114 = FStar_Options.print_implicits () in
               if uu____1114 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1128  ->
                       match uu____1128 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1158 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1158 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1166 = FStar_Options.print_implicits () in
               if uu____1166 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1172 =
                 FStar_All.pipe_right xs2
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1172 FStar_List.rev in
             let rec aux body3 uu___236_1191 =
               match uu___236_1191 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1207 =
          let uu____1212 =
            let uu____1213 = FStar_Syntax_Syntax.mk_binder x in [uu____1213] in
          FStar_Syntax_Subst.open_term uu____1212 phi in
        (match uu____1207 with
         | (x1,phi1) ->
             let b =
               let uu____1217 =
                 let uu____1220 = FStar_List.hd x1 in
                 resugar_binder uu____1220 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1217 in
             let uu____1225 =
               let uu____1226 =
                 let uu____1231 = resugar_term phi1 in (b, uu____1231) in
               FStar_Parser_AST.Refine uu____1226 in
             mk1 uu____1225)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___237_1273 =
          match uu___237_1273 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1343 -> failwith "last of an empty list" in
        let rec last_two uu___238_1379 =
          match uu___238_1379 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1410::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1487::t1 -> last_two t1 in
        let rec last_three uu___239_1528 =
          match uu___239_1528 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1559::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1586::uu____1587::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1695::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1781  ->
                    match uu____1781 with
                    | (e2,qual) ->
                        let uu____1800 = resugar_term e2 in
                        (uu____1800, qual))) in
          let e2 = resugar_term e1 in
          let res_impl desugared_tm qual =
            let uu____1815 = resugar_imp qual in
            match uu____1815 with
            | FStar_Pervasives_Native.Some imp -> imp
            | FStar_Pervasives_Native.None  ->
                ((let uu____1820 =
                    let uu____1821 = parser_term_to_string desugared_tm in
                    FStar_Util.format1
                      "Inaccessible argument %s in function application"
                      uu____1821 in
                  FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1820);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1834  ->
                 match uu____1834 with
                 | (x,qual) ->
                     let uu____1847 =
                       let uu____1848 =
                         let uu____1855 = res_impl x qual in
                         (acc, x, uu____1855) in
                       FStar_Parser_AST.App uu____1848 in
                     mk1 uu____1847) e2 args2 in
        let args1 =
          let uu____1865 = FStar_Options.print_implicits () in
          if uu____1865 then args else filter_imp args in
        let uu____1877 = resugar_term_as_op e in
        (match uu____1877 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1888) ->
             (match args1 with
              | (fst1,uu____1894)::(snd1,uu____1896)::rest ->
                  let e1 =
                    let uu____1927 =
                      let uu____1928 =
                        let uu____1935 =
                          let uu____1938 = resugar_term fst1 in
                          let uu____1939 =
                            let uu____1942 = resugar_term snd1 in
                            [uu____1942] in
                          uu____1938 :: uu____1939 in
                        ((FStar_Ident.id_of_text "*"), uu____1935) in
                      FStar_Parser_AST.Op uu____1928 in
                    mk1 uu____1927 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1955  ->
                         match uu____1955 with
                         | (x,uu____1961) ->
                             let uu____1962 =
                               let uu____1963 =
                                 let uu____1970 =
                                   let uu____1973 =
                                     let uu____1976 = resugar_term x in
                                     [uu____1976] in
                                   e1 :: uu____1973 in
                                 ((FStar_Ident.id_of_text "*"), uu____1970) in
                               FStar_Parser_AST.Op uu____1963 in
                             mk1 uu____1962) e1 rest
              | uu____1979 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1988) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2014)::[] -> b
               | uu____2031 -> failwith "wrong arguments to dtuple" in
             let uu____2042 =
               let uu____2043 = FStar_Syntax_Subst.compress body in
               uu____2043.FStar_Syntax_Syntax.n in
             (match uu____2042 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2048) ->
                  let uu____2069 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2069 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2077 = FStar_Options.print_implicits () in
                         if uu____2077 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2089 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2110  ->
                            match uu____2110 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2122) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2128) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2133 = FStar_List.hd args1 in
             (match uu____2133 with
              | (t1,uu____2147) ->
                  let uu____2152 =
                    let uu____2153 = FStar_Syntax_Subst.compress t1 in
                    uu____2153.FStar_Syntax_Syntax.n in
                  (match uu____2152 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2158 =
                         let uu____2159 =
                           let uu____2164 = resugar_term t1 in
                           (uu____2164, f) in
                         FStar_Parser_AST.Project uu____2159 in
                       mk1 uu____2158
                   | uu____2165 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2166) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2186 =
               match new_args with
               | (a1,uu____2204)::(a2,uu____2206)::[] -> (a1, a2)
               | uu____2237 -> failwith "wrong arguments to try_with" in
             (match uu____2186 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2268 =
                      let uu____2269 = FStar_Syntax_Subst.compress term in
                      uu____2269.FStar_Syntax_Syntax.n in
                    match uu____2268 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2274) ->
                        let uu____2295 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2295 with | (x1,e2) -> e2)
                    | uu____2302 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2304 = decomp body in resugar_term uu____2304 in
                  let handler1 =
                    let uu____2306 = decomp handler in
                    resugar_term uu____2306 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2312,uu____2313,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2345,uu____2346,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2367 =
                          let uu____2368 =
                            let uu____2377 = resugar_body t11 in
                            (uu____2377, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2368 in
                        mk1 uu____2367
                    | uu____2380 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2435 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2465) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2471) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2556 -> (xs, pat, t1) in
             let resugar body =
               let uu____2567 =
                 let uu____2568 = FStar_Syntax_Subst.compress body in
                 uu____2568.FStar_Syntax_Syntax.n in
               match uu____2567 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2573) ->
                   let uu____2594 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2594 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2602 = FStar_Options.print_implicits () in
                          if uu____2602 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2611 =
                          let uu____2620 =
                            let uu____2621 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2621.FStar_Syntax_Syntax.n in
                          match uu____2620 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2690  ->
                                                 match uu____2690 with
                                                 | (e2,uu____2696) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2699) ->
                                    let uu____2700 =
                                      let uu____2703 =
                                        let uu____2704 = name s r in
                                        mk1 uu____2704 in
                                      [uu____2703] in
                                    [uu____2700]
                                | uu____2709 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2718 ->
                              let uu____2719 = resugar_term body2 in
                              ([], uu____2719) in
                        (match uu____2611 with
                         | (pats,body3) ->
                             let uu____2736 = uncurry xs3 pats body3 in
                             (match uu____2736 with
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
               | uu____2784 ->
                   if op = "forall"
                   then
                     let uu____2785 =
                       let uu____2786 =
                         let uu____2799 = resugar_term body in
                         ([], [[]], uu____2799) in
                       FStar_Parser_AST.QForall uu____2786 in
                     mk1 uu____2785
                   else
                     (let uu____2811 =
                        let uu____2812 =
                          let uu____2825 = resugar_term body in
                          ([], [[]], uu____2825) in
                        FStar_Parser_AST.QExists uu____2812 in
                      mk1 uu____2811) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2852)::[] -> resugar b
                | uu____2869 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2879) ->
             let uu____2884 = FStar_List.hd args1 in
             (match uu____2884 with | (e1,uu____2898) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2943  ->
                       match uu____2943 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____2950 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2950 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2957 =
                         let uu____2958 =
                           let uu____2965 =
                             let uu____2968 = last1 args1 in
                             resugar uu____2968 in
                           (op1, uu____2965) in
                         FStar_Parser_AST.Op uu____2958 in
                       mk1 uu____2957
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2983 =
                         let uu____2984 =
                           let uu____2991 =
                             let uu____2994 = last_two args1 in
                             resugar uu____2994 in
                           (op1, uu____2991) in
                         FStar_Parser_AST.Op uu____2984 in
                       mk1 uu____2983
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3009 =
                         let uu____3010 =
                           let uu____3017 =
                             let uu____3020 = last_three args1 in
                             resugar uu____3020 in
                           (op1, uu____3017) in
                         FStar_Parser_AST.Op uu____3010 in
                       mk1 uu____3009
                   | uu____3029 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3036 =
                    let uu____3037 =
                      let uu____3044 =
                        let uu____3047 = last_two args1 in resugar uu____3047 in
                      (op1, uu____3044) in
                    FStar_Parser_AST.Op uu____3037 in
                  mk1 uu____3036
              | uu____3056 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3059,t1)::[]) ->
        let bnds =
          let uu____3132 =
            let uu____3137 = resugar_pat pat in
            let uu____3138 = resugar_term e in (uu____3137, uu____3138) in
          [uu____3132] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3156,t1)::(pat2,uu____3159,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3255 =
          let uu____3256 =
            let uu____3263 = resugar_term e in
            let uu____3264 = resugar_term t1 in
            let uu____3265 = resugar_term t2 in
            (uu____3263, uu____3264, uu____3265) in
          FStar_Parser_AST.If uu____3256 in
        mk1 uu____3255
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3323 =
          match uu____3323 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3354 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3354 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3358 =
          let uu____3359 =
            let uu____3374 = resugar_term e in
            let uu____3375 = FStar_List.map resugar_branch branches in
            (uu____3374, uu____3375) in
          FStar_Parser_AST.Match uu____3359 in
        mk1 uu____3358
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3415) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3482 =
          let uu____3483 =
            let uu____3492 = resugar_term e in (uu____3492, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3483 in
        mk1 uu____3482
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3516 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3516 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3541 =
                 let uu____3546 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3546 in
               match uu____3541 with
               | (univs1,td) ->
                   let uu____3557 =
                     let uu____3566 =
                       let uu____3567 = FStar_Syntax_Subst.compress td in
                       uu____3567.FStar_Syntax_Syntax.n in
                     match uu____3566 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3578,(t1,uu____3580)::(d,uu____3582)::[]) ->
                         (t1, d)
                     | uu____3625 -> failwith "wrong let binding format" in
                   (match uu____3557 with
                    | (typ,def) ->
                        let uu____3652 =
                          let uu____3659 =
                            let uu____3660 = FStar_Syntax_Subst.compress def in
                            uu____3660.FStar_Syntax_Syntax.n in
                          match uu____3659 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3671) ->
                              let uu____3692 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3692 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3706 =
                                       FStar_Options.print_implicits () in
                                     if uu____3706 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3708 -> ([], def, false) in
                        (match uu____3652 with
                         | (binders,term,is_pat_app) ->
                             let uu____3732 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3743 =
                                     let uu____3744 =
                                       let uu____3745 =
                                         let uu____3752 =
                                           bv_as_unique_ident bv in
                                         (uu____3752,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3745 in
                                     mk_pat uu____3744 in
                                   (uu____3743, term) in
                             (match uu____3732 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3788  ->
                                              match uu____3788 with
                                              | (bv,q) ->
                                                  let uu____3803 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3803
                                                    (fun q1  ->
                                                       let uu____3815 =
                                                         let uu____3816 =
                                                           let uu____3823 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3823, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3816 in
                                                       mk_pat uu____3815))) in
                                    let uu____3826 =
                                      let uu____3831 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3831) in
                                    let uu____3834 =
                                      universe_to_string univs1 in
                                    (uu____3826, uu____3834)
                                  else
                                    (let uu____3840 =
                                       let uu____3845 = resugar_term term1 in
                                       (pat, uu____3845) in
                                     let uu____3846 =
                                       universe_to_string univs1 in
                                     (uu____3840, uu____3846))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3892 =
                   let uu____3893 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3893 in
                 if uu____3892
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___240_3913  ->
                      match uu___240_3913 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3954) ->
        let s =
          let uu____3980 =
            let uu____3981 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3981 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____3980 in
        let uu____3982 = mk1 FStar_Parser_AST.Wild in label s uu____3982
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___241_3992 =
          match uu___241_3992 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4013 =
                  let uu____4014 = FStar_Syntax_Subst.compress h in
                  uu____4014.FStar_Syntax_Syntax.n in
                match uu____4013 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4034 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4034, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4057 = head_fv_universes_args h1 in
                    (match uu____4057 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4145 = head_fv_universes_args head1 in
                    (match uu____4145 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4217 ->
                    let uu____4218 =
                      let uu____4219 =
                        let uu____4220 =
                          let uu____4221 = resugar_term h in
                          parser_term_to_string uu____4221 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4220 in
                      FStar_Errors.Err uu____4219 in
                    FStar_Exn.raise uu____4218 in
              let uu____4238 =
                try
                  let uu____4290 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4290
                with
                | FStar_Errors.Err uu____4311 ->
                    let uu____4312 =
                      let uu____4313 =
                        let uu____4318 =
                          let uu____4319 =
                            let uu____4320 = resugar_term e in
                            parser_term_to_string uu____4320 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4319 in
                        (uu____4318, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4313 in
                    FStar_Exn.raise uu____4312 in
              (match uu____4238 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4374 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4374, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4398  ->
                          match uu____4398 with
                          | (t1,q) ->
                              let uu____4417 = resugar_imp q in
                              (match uu____4417 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4427 =
                                     let uu____4432 = resugar_term t1 in
                                     (uu____4432, rimp) in
                                   FStar_Pervasives_Native.Some uu____4427
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4448 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4450 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4450) in
                     if uu____4448
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4473,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4498 =
                      let uu____4499 =
                        let uu____4508 = resugar_seq t11 in
                        (uu____4508, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4499 in
                    mk1 uu____4498
                | uu____4511 -> t1 in
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
               | uu____4533 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4535 =
                let uu____4536 = FStar_Syntax_Subst.compress e in
                uu____4536.FStar_Syntax_Syntax.n in
              (match uu____4535 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4540;
                      FStar_Syntax_Syntax.vars = uu____4541;_},(term,uu____4543)::[])
                   -> resugar_term term
               | uu____4572 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4610  ->
                       match uu____4610 with
                       | (x,uu____4616) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4618,p) ->
             let uu____4620 =
               let uu____4621 =
                 let uu____4628 = resugar_term e in (uu____4628, l, p) in
               FStar_Parser_AST.Labeled uu____4621 in
             mk1 uu____4620
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4630,s,uu____4632) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4637 ->
                  (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                     "Meta_alien was not a Tm_unknown";
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4646 =
               let uu____4647 =
                 let uu____4656 = resugar_term e in
                 let uu____4657 =
                   let uu____4658 =
                     let uu____4659 =
                       let uu____4670 =
                         let uu____4677 =
                           let uu____4682 = resugar_term t1 in
                           (uu____4682, FStar_Parser_AST.Nothing) in
                         [uu____4677] in
                       (name1, uu____4670) in
                     FStar_Parser_AST.Construct uu____4659 in
                   mk1 uu____4658 in
                 (uu____4656, uu____4657, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4647 in
             mk1 uu____4646
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4700,t1) ->
             let uu____4706 =
               let uu____4707 =
                 let uu____4716 = resugar_term e in
                 let uu____4717 =
                   let uu____4718 =
                     let uu____4719 =
                       let uu____4730 =
                         let uu____4737 =
                           let uu____4742 = resugar_term t1 in
                           (uu____4742, FStar_Parser_AST.Nothing) in
                         [uu____4737] in
                       (name1, uu____4730) in
                     FStar_Parser_AST.Construct uu____4719 in
                   mk1 uu____4718 in
                 (uu____4716, uu____4717, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4707 in
             mk1 uu____4706)
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
             let uu____4790 = FStar_Options.print_universes () in
             if uu____4790
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
             let uu____4851 = FStar_Options.print_universes () in
             if uu____4851
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
          let uu____4892 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4892, FStar_Parser_AST.Nothing) in
        let uu____4893 = FStar_Options.print_effect_args () in
        if uu____4893
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
                    let uu____4980 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____4980, (FStar_Pervasives_Native.snd post)) in
                  let uu____4989 =
                    let uu____4998 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____4998 then [] else [pre] in
                  let uu____5028 =
                    let uu____5037 =
                      let uu____5046 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5046 then [] else [pats] in
                    FStar_List.append [post1] uu____5037 in
                  FStar_List.append uu____4989 uu____5028
              | uu____5100 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5129  ->
                 match uu____5129 with
                 | (e,uu____5139) ->
                     let uu____5140 = resugar_term e in
                     (uu____5140, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___242_5161 =
            match uu___242_5161 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5194 = resugar_term e in
                       (uu____5194, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5199 -> aux l tl1) in
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
      let uu____5244 = b in
      match uu____5244 with
      | (x,aq) ->
          let uu____5249 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5249
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5263 =
                     let uu____5264 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5264 in
                   FStar_Parser_AST.mk_binder uu____5263 r
                     FStar_Parser_AST.Type_level imp
               | uu____5265 ->
                   let uu____5266 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5266
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5268 =
                        let uu____5269 =
                          let uu____5274 = bv_as_unique_ident x in
                          (uu____5274, e) in
                        FStar_Parser_AST.Annotated uu____5269 in
                      FStar_Parser_AST.mk_binder uu____5268 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5283 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5283 in
      let uu____5284 =
        let uu____5285 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5285.FStar_Syntax_Syntax.n in
      match uu____5284 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5293 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5293
          else
            (let uu____5295 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5295
               (fun aq  ->
                  let uu____5307 =
                    let uu____5308 =
                      let uu____5309 =
                        let uu____5316 = bv_as_unique_ident x in
                        (uu____5316, aq) in
                      FStar_Parser_AST.PatVar uu____5309 in
                    mk1 uu____5308 in
                  FStar_Pervasives_Native.Some uu____5307))
      | uu____5319 ->
          let uu____5320 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5320
            (fun aq  ->
               let pat =
                 let uu____5335 =
                   let uu____5336 =
                     let uu____5343 = bv_as_unique_ident x in
                     (uu____5343, aq) in
                   FStar_Parser_AST.PatVar uu____5336 in
                 mk1 uu____5335 in
               let uu____5346 = FStar_Options.print_bound_var_types () in
               if uu____5346
               then
                 let uu____5349 =
                   let uu____5350 =
                     let uu____5351 =
                       let uu____5356 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5356) in
                     FStar_Parser_AST.PatAscribed uu____5351 in
                   mk1 uu____5350 in
                 FStar_Pervasives_Native.Some uu____5349
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
              (fun uu____5433  ->
                 match uu____5433 with
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
              (fun uu____5468  ->
                 match uu____5468 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5475 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5475
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5481;
             FStar_Syntax_Syntax.fv_delta = uu____5482;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5509 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5509 FStar_List.rev in
          let args1 =
            let uu____5525 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5545  ->
                      match uu____5545 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5525 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5615 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5615
            | (hd1::tl1,hd2::tl2) ->
                let uu____5638 = map21 tl1 tl2 in (hd1, hd2) :: uu____5638 in
          let args2 =
            let uu____5656 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5656 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5707  ->
                 match uu____5707 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5717 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5717 with
           | FStar_Pervasives_Native.Some (op,uu____5725) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5734 =
                 let uu____5735 =
                   let uu____5742 = bv_as_unique_ident v1 in
                   let uu____5743 = to_arg_qual imp_opt in
                   (uu____5742, uu____5743) in
                 FStar_Parser_AST.PatVar uu____5735 in
               mk1 uu____5734)
      | FStar_Syntax_Syntax.Pat_wild uu____5748 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5756 =
              let uu____5757 =
                let uu____5764 = bv_as_unique_ident bv in
                (uu____5764,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5757 in
            mk1 uu____5756 in
          let uu____5767 = FStar_Options.print_bound_var_types () in
          if uu____5767
          then
            let uu____5768 =
              let uu____5769 =
                let uu____5774 = resugar_term term in (pat, uu____5774) in
              FStar_Parser_AST.PatAscribed uu____5769 in
            mk1 uu____5768
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___243_5780  ->
    match uu___243_5780 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5789 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5790 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5791 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5796 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5805 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5814 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___244_5817  ->
    match uu___244_5817 with
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
          (tylid,uvs,bs,t,uu____5844,datacons) ->
          let uu____5854 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5881,uu____5882,uu____5883,inductive_lid,uu____5885,uu____5886)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5891 -> failwith "unexpected")) in
          (match uu____5854 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5910 = FStar_Options.print_implicits () in
                 if uu____5910 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5920 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___245_5925  ->
                           match uu___245_5925 with
                           | FStar_Syntax_Syntax.RecordType uu____5926 ->
                               true
                           | uu____5935 -> false)) in
                 if uu____5920
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5983,univs1,term,uu____5986,num,uu____5988)
                         ->
                         let uu____5993 =
                           let uu____5994 = FStar_Syntax_Subst.compress term in
                           uu____5994.FStar_Syntax_Syntax.n in
                         (match uu____5993 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6008) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6069  ->
                                        match uu____6069 with
                                        | (b,qual) ->
                                            let uu____6084 =
                                              let uu____6085 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6085 in
                                            let uu____6086 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6084, uu____6086,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6097 -> failwith "unexpected")
                     | uu____6108 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6229,num,uu____6231) ->
                          let c =
                            let uu____6249 =
                              let uu____6252 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6252 in
                            ((l.FStar_Ident.ident), uu____6249,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6269 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6345 ->
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
        let uu____6363 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6363;
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
      let uu____6376 = ts in
      match uu____6376 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6384 =
            let uu____6385 =
              let uu____6398 =
                let uu____6407 =
                  let uu____6414 =
                    let uu____6415 =
                      let uu____6428 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6428) in
                    FStar_Parser_AST.TyconAbbrev uu____6415 in
                  (uu____6414, FStar_Pervasives_Native.None) in
                [uu____6407] in
              (false, uu____6398) in
            FStar_Parser_AST.Tycon uu____6385 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6384
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
            let uu____6482 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6482 with
            | (bs,action_defn) ->
                let uu____6489 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6489 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6497 = FStar_Options.print_implicits () in
                       if uu____6497
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6502 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6502 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6516 =
                           let uu____6527 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6527,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6516 in
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
          let uu____6601 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6601 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6609 = FStar_Options.print_implicits () in
                if uu____6609 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6614 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6614 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6671) ->
        let uu____6680 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6702 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6719 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6726 -> false
                  | uu____6741 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6680 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6773 se1 =
               match uu____6773 with
               | (datacon_ses1,tycons) ->
                   let uu____6799 = resugar_typ datacon_ses1 se1 in
                   (match uu____6799 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6814 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6814 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6849 =
                         let uu____6850 =
                           let uu____6851 =
                             let uu____6864 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6864) in
                           FStar_Parser_AST.Tycon uu____6851 in
                         decl'_to_decl se uu____6850 in
                       FStar_Pervasives_Native.Some uu____6849
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6895,uu____6896,uu____6897,uu____6898,uu____6899)
                            ->
                            let uu____6904 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6904
                        | uu____6907 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6910 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6916) ->
        let uu____6921 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___246_6927  ->
                  match uu___246_6927 with
                  | FStar_Syntax_Syntax.Projector (uu____6928,uu____6929) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6930 -> true
                  | uu____6931 -> false)) in
        if uu____6921
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6954) ->
               let uu____6967 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6967
           | uu____6974 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6978,fml) ->
        let uu____6980 =
          let uu____6981 =
            let uu____6982 =
              let uu____6987 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6987) in
            FStar_Parser_AST.Assume uu____6982 in
          decl'_to_decl se uu____6981 in
        FStar_Pervasives_Native.Some uu____6980
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6989 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6989
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6991 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6991
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____7000,t) ->
              let uu____7012 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7012
          | uu____7013 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7021,t) ->
              let uu____7033 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7033
          | uu____7034 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7058 -> failwith "Should not happen hopefully" in
        let uu____7067 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7067
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7077 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7077 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7087 = FStar_Options.print_implicits () in
               if uu____7087 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7096 =
               let uu____7097 =
                 let uu____7098 =
                   let uu____7111 =
                     let uu____7120 =
                       let uu____7127 =
                         let uu____7128 =
                           let uu____7141 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7141) in
                         FStar_Parser_AST.TyconAbbrev uu____7128 in
                       (uu____7127, FStar_Pervasives_Native.None) in
                     [uu____7120] in
                   (false, uu____7111) in
                 FStar_Parser_AST.Tycon uu____7098 in
               decl'_to_decl se uu____7097 in
             FStar_Pervasives_Native.Some uu____7096)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7169 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7169
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7173 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___247_7179  ->
                  match uu___247_7179 with
                  | FStar_Syntax_Syntax.Projector (uu____7180,uu____7181) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7182 -> true
                  | uu____7183 -> false)) in
        if uu____7173
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7188 =
               (let uu____7191 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7191) || (FStar_List.isEmpty uvs) in
             if uu____7188
             then resugar_term t
             else
               (let uu____7193 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7193 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7201 = resugar_term t1 in
                    label universes uu____7201) in
           let uu____7202 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7202)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7203 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7220 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7235 -> FStar_Pervasives_Native.None