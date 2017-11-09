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
      || FStar_Options.print_real_names()
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
             let rec aux body3 uu___236_1170 =
               match uu___236_1170 with
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
        let rec last1 uu___237_1252 =
          match uu___237_1252 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1322 -> failwith "last of an empty list" in
        let rec last_two uu___238_1358 =
          match uu___238_1358 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1389::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1466::t1 -> last_two t1 in
        let rec last_three uu___239_1507 =
          match uu___239_1507 with
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
                    let uu____1800 = parser_term_to_string desugared_tm in
                    FStar_Util.format1
                      "Inaccessible argument %s in function application"
                      uu____1800 in
                  FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1799);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1813  ->
                 match uu____1813 with
                 | (x,qual) ->
                     let uu____1826 =
                       let uu____1827 =
                         let uu____1834 = res_impl x qual in
                         (acc, x, uu____1834) in
                       FStar_Parser_AST.App uu____1827 in
                     mk1 uu____1826) e2 args2 in
        let args1 =
          let uu____1844 = FStar_Options.print_implicits () in
          if uu____1844 then args else filter_imp args in
        let uu____1856 = resugar_term_as_op e in
        (match uu____1856 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1867) ->
             (match args1 with
              | (fst1,uu____1873)::(snd1,uu____1875)::rest ->
                  let e1 =
                    let uu____1906 =
                      let uu____1907 =
                        let uu____1914 =
                          let uu____1917 = resugar_term fst1 in
                          let uu____1918 =
                            let uu____1921 = resugar_term snd1 in
                            [uu____1921] in
                          uu____1917 :: uu____1918 in
                        ((FStar_Ident.id_of_text "*"), uu____1914) in
                      FStar_Parser_AST.Op uu____1907 in
                    mk1 uu____1906 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1934  ->
                         match uu____1934 with
                         | (x,uu____1940) ->
                             let uu____1941 =
                               let uu____1942 =
                                 let uu____1949 =
                                   let uu____1952 =
                                     let uu____1955 = resugar_term x in
                                     [uu____1955] in
                                   e1 :: uu____1952 in
                                 ((FStar_Ident.id_of_text "*"), uu____1949) in
                               FStar_Parser_AST.Op uu____1942 in
                             mk1 uu____1941) e1 rest
              | uu____1958 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1967) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1993)::[] -> b
               | uu____2010 -> failwith "wrong arguments to dtuple" in
             let uu____2021 =
               let uu____2022 = FStar_Syntax_Subst.compress body in
               uu____2022.FStar_Syntax_Syntax.n in
             (match uu____2021 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2027) ->
                  let uu____2048 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2048 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2056 = FStar_Options.print_implicits () in
                         if uu____2056 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2068 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2089  ->
                            match uu____2089 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2101) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2107) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2112 = FStar_List.hd args1 in
             (match uu____2112 with
              | (t1,uu____2126) ->
                  let uu____2131 =
                    let uu____2132 = FStar_Syntax_Subst.compress t1 in
                    uu____2132.FStar_Syntax_Syntax.n in
                  (match uu____2131 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2137 =
                         let uu____2138 =
                           let uu____2143 = resugar_term t1 in
                           (uu____2143, f) in
                         FStar_Parser_AST.Project uu____2138 in
                       mk1 uu____2137
                   | uu____2144 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2145) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2165 =
               match new_args with
               | (a1,uu____2183)::(a2,uu____2185)::[] -> (a1, a2)
               | uu____2216 -> failwith "wrong arguments to try_with" in
             (match uu____2165 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2247 =
                      let uu____2248 = FStar_Syntax_Subst.compress term in
                      uu____2248.FStar_Syntax_Syntax.n in
                    match uu____2247 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2253) ->
                        let uu____2274 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2274 with | (x1,e2) -> e2)
                    | uu____2281 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2283 = decomp body in resugar_term uu____2283 in
                  let handler1 =
                    let uu____2285 = decomp handler in
                    resugar_term uu____2285 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2291,uu____2292,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2324,uu____2325,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2346 =
                          let uu____2347 =
                            let uu____2356 = resugar_body t11 in
                            (uu____2356, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2347 in
                        mk1 uu____2346
                    | uu____2359 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2414 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2444) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2450) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2535 -> (xs, pat, t1) in
             let resugar body =
               let uu____2546 =
                 let uu____2547 = FStar_Syntax_Subst.compress body in
                 uu____2547.FStar_Syntax_Syntax.n in
               match uu____2546 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2552) ->
                   let uu____2573 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2573 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2581 = FStar_Options.print_implicits () in
                          if uu____2581 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2590 =
                          let uu____2599 =
                            let uu____2600 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2600.FStar_Syntax_Syntax.n in
                          match uu____2599 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2669  ->
                                                 match uu____2669 with
                                                 | (e2,uu____2675) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2678) ->
                                    let uu____2679 =
                                      let uu____2682 =
                                        let uu____2683 = name s r in
                                        mk1 uu____2683 in
                                      [uu____2682] in
                                    [uu____2679]
                                | uu____2688 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2697 ->
                              let uu____2698 = resugar_term body2 in
                              ([], uu____2698) in
                        (match uu____2590 with
                         | (pats,body3) ->
                             let uu____2715 = uncurry xs3 pats body3 in
                             (match uu____2715 with
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
               | uu____2763 ->
                   if op = "forall"
                   then
                     let uu____2764 =
                       let uu____2765 =
                         let uu____2778 = resugar_term body in
                         ([], [[]], uu____2778) in
                       FStar_Parser_AST.QForall uu____2765 in
                     mk1 uu____2764
                   else
                     (let uu____2790 =
                        let uu____2791 =
                          let uu____2804 = resugar_term body in
                          ([], [[]], uu____2804) in
                        FStar_Parser_AST.QExists uu____2791 in
                      mk1 uu____2790) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2831)::[] -> resugar b
                | uu____2848 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2858) ->
             let uu____2863 = FStar_List.hd args1 in
             (match uu____2863 with | (e1,uu____2877) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2922  ->
                       match uu____2922 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____2929 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2929 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2936 =
                         let uu____2937 =
                           let uu____2944 =
                             let uu____2947 = last1 args1 in
                             resugar uu____2947 in
                           (op1, uu____2944) in
                         FStar_Parser_AST.Op uu____2937 in
                       mk1 uu____2936
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2962 =
                         let uu____2963 =
                           let uu____2970 =
                             let uu____2973 = last_two args1 in
                             resugar uu____2973 in
                           (op1, uu____2970) in
                         FStar_Parser_AST.Op uu____2963 in
                       mk1 uu____2962
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2988 =
                         let uu____2989 =
                           let uu____2996 =
                             let uu____2999 = last_three args1 in
                             resugar uu____2999 in
                           (op1, uu____2996) in
                         FStar_Parser_AST.Op uu____2989 in
                       mk1 uu____2988
                   | uu____3008 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3015 =
                    let uu____3016 =
                      let uu____3023 =
                        let uu____3026 = last_two args1 in resugar uu____3026 in
                      (op1, uu____3023) in
                    FStar_Parser_AST.Op uu____3016 in
                  mk1 uu____3015
              | uu____3035 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3038,t1)::[]) ->
        let bnds =
          let uu____3111 =
            let uu____3116 = resugar_pat pat in
            let uu____3117 = resugar_term e in (uu____3116, uu____3117) in
          [uu____3111] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3135,t1)::(pat2,uu____3138,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3234 =
          let uu____3235 =
            let uu____3242 = resugar_term e in
            let uu____3243 = resugar_term t1 in
            let uu____3244 = resugar_term t2 in
            (uu____3242, uu____3243, uu____3244) in
          FStar_Parser_AST.If uu____3235 in
        mk1 uu____3234
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3302 =
          match uu____3302 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3333 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3333 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3337 =
          let uu____3338 =
            let uu____3353 = resugar_term e in
            let uu____3354 = FStar_List.map resugar_branch branches in
            (uu____3353, uu____3354) in
          FStar_Parser_AST.Match uu____3338 in
        mk1 uu____3337
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3394) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3461 =
          let uu____3462 =
            let uu____3471 = resugar_term e in (uu____3471, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3462 in
        mk1 uu____3461
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3495 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3495 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3520 =
                 let uu____3525 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3525 in
               match uu____3520 with
               | (univs1,td) ->
                   let uu____3536 =
                     let uu____3545 =
                       let uu____3546 = FStar_Syntax_Subst.compress td in
                       uu____3546.FStar_Syntax_Syntax.n in
                     match uu____3545 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3557,(t1,uu____3559)::(d,uu____3561)::[]) ->
                         (t1, d)
                     | uu____3604 -> failwith "wrong let binding format" in
                   (match uu____3536 with
                    | (typ,def) ->
                        let uu____3631 =
                          let uu____3638 =
                            let uu____3639 = FStar_Syntax_Subst.compress def in
                            uu____3639.FStar_Syntax_Syntax.n in
                          match uu____3638 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3650) ->
                              let uu____3671 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3671 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3685 =
                                       FStar_Options.print_implicits () in
                                     if uu____3685 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3687 -> ([], def, false) in
                        (match uu____3631 with
                         | (binders,term,is_pat_app) ->
                             let uu____3711 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3722 =
                                     let uu____3723 =
                                       let uu____3724 =
                                         let uu____3731 =
                                           bv_as_unique_ident bv in
                                         (uu____3731,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3724 in
                                     mk_pat uu____3723 in
                                   (uu____3722, term) in
                             (match uu____3711 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3767  ->
                                              match uu____3767 with
                                              | (bv,q) ->
                                                  let uu____3782 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3782
                                                    (fun q1  ->
                                                       let uu____3794 =
                                                         let uu____3795 =
                                                           let uu____3802 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3802, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3795 in
                                                       mk_pat uu____3794))) in
                                    let uu____3805 =
                                      let uu____3810 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3810) in
                                    let uu____3813 =
                                      universe_to_string univs1 in
                                    (uu____3805, uu____3813)
                                  else
                                    (let uu____3819 =
                                       let uu____3824 = resugar_term term1 in
                                       (pat, uu____3824) in
                                     let uu____3825 =
                                       universe_to_string univs1 in
                                     (uu____3819, uu____3825))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3871 =
                   let uu____3872 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3872 in
                 if uu____3871
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___240_3892  ->
                      match uu___240_3892 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3933) ->
        let s =
          let uu____3959 =
            let uu____3960 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3960 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____3959 in
        let uu____3961 = mk1 FStar_Parser_AST.Wild in label s uu____3961
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___241_3971 =
          match uu___241_3971 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____3992 =
                  let uu____3993 = FStar_Syntax_Subst.compress h in
                  uu____3993.FStar_Syntax_Syntax.n in
                match uu____3992 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4013 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4013, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4036 = head_fv_universes_args h1 in
                    (match uu____4036 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4124 = head_fv_universes_args head1 in
                    (match uu____4124 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4196 ->
                    let uu____4197 =
                      let uu____4198 =
                        let uu____4199 =
                          let uu____4200 = resugar_term h in
                          parser_term_to_string uu____4200 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4199 in
                      FStar_Errors.Err uu____4198 in
                    FStar_Exn.raise uu____4197 in
              let uu____4217 =
                try
                  let uu____4269 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4269
                with
                | FStar_Errors.Err uu____4290 ->
                    let uu____4291 =
                      let uu____4292 =
                        let uu____4297 =
                          let uu____4298 =
                            let uu____4299 = resugar_term e in
                            parser_term_to_string uu____4299 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4298 in
                        (uu____4297, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4292 in
                    FStar_Exn.raise uu____4291 in
              (match uu____4217 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4353 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4353, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4377  ->
                          match uu____4377 with
                          | (t1,q) ->
                              let uu____4396 = resugar_imp q in
                              (match uu____4396 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4406 =
                                     let uu____4411 = resugar_term t1 in
                                     (uu____4411, rimp) in
                                   FStar_Pervasives_Native.Some uu____4406
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4427 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4429 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4429) in
                     if uu____4427
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4452,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4477 =
                      let uu____4478 =
                        let uu____4487 = resugar_seq t11 in
                        (uu____4487, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4478 in
                    mk1 uu____4477
                | uu____4490 -> t1 in
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
               | uu____4512 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4514 =
                let uu____4515 = FStar_Syntax_Subst.compress e in
                uu____4515.FStar_Syntax_Syntax.n in
              (match uu____4514 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4519;
                      FStar_Syntax_Syntax.vars = uu____4520;_},(term,uu____4522)::[])
                   -> resugar_term term
               | uu____4551 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4589  ->
                       match uu____4589 with
                       | (x,uu____4595) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4597,p) ->
             let uu____4599 =
               let uu____4600 =
                 let uu____4607 = resugar_term e in (uu____4607, l, p) in
               FStar_Parser_AST.Labeled uu____4600 in
             mk1 uu____4599
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4609,s,uu____4611) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4616 ->
                  (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                     "Meta_alien was not a Tm_unknown";
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4625 =
               let uu____4626 =
                 let uu____4635 = resugar_term e in
                 let uu____4636 =
                   let uu____4637 =
                     let uu____4638 =
                       let uu____4649 =
                         let uu____4656 =
                           let uu____4661 = resugar_term t1 in
                           (uu____4661, FStar_Parser_AST.Nothing) in
                         [uu____4656] in
                       (name1, uu____4649) in
                     FStar_Parser_AST.Construct uu____4638 in
                   mk1 uu____4637 in
                 (uu____4635, uu____4636, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4626 in
             mk1 uu____4625
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4679,t1) ->
             let uu____4685 =
               let uu____4686 =
                 let uu____4695 = resugar_term e in
                 let uu____4696 =
                   let uu____4697 =
                     let uu____4698 =
                       let uu____4709 =
                         let uu____4716 =
                           let uu____4721 = resugar_term t1 in
                           (uu____4721, FStar_Parser_AST.Nothing) in
                         [uu____4716] in
                       (name1, uu____4709) in
                     FStar_Parser_AST.Construct uu____4698 in
                   mk1 uu____4697 in
                 (uu____4695, uu____4696, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4686 in
             mk1 uu____4685)
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
             let uu____4769 = FStar_Options.print_universes () in
             if uu____4769
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
             let uu____4830 = FStar_Options.print_universes () in
             if uu____4830
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
          let uu____4871 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4871, FStar_Parser_AST.Nothing) in
        let uu____4872 = FStar_Options.print_effect_args () in
        if uu____4872
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
                    let uu____4959 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____4959, (FStar_Pervasives_Native.snd post)) in
                  let uu____4968 =
                    let uu____4977 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____4977 then [] else [pre] in
                  let uu____5007 =
                    let uu____5016 =
                      let uu____5025 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5025 then [] else [pats] in
                    FStar_List.append [post1] uu____5016 in
                  FStar_List.append uu____4968 uu____5007
              | uu____5079 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5108  ->
                 match uu____5108 with
                 | (e,uu____5118) ->
                     let uu____5119 = resugar_term e in
                     (uu____5119, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___242_5140 =
            match uu___242_5140 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5173 = resugar_term e in
                       (uu____5173, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5178 -> aux l tl1) in
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
      let uu____5223 = b in
      match uu____5223 with
      | (x,aq) ->
          let uu____5228 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5228
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5242 =
                     let uu____5243 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5243 in
                   FStar_Parser_AST.mk_binder uu____5242 r
                     FStar_Parser_AST.Type_level imp
               | uu____5244 ->
                   let uu____5245 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5245
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5247 =
                        let uu____5248 =
                          let uu____5253 = bv_as_unique_ident x in
                          (uu____5253, e) in
                        FStar_Parser_AST.Annotated uu____5248 in
                      FStar_Parser_AST.mk_binder uu____5247 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5262 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5262 in
      let uu____5263 =
        let uu____5264 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5264.FStar_Syntax_Syntax.n in
      match uu____5263 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5272 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5272
          else
            (let uu____5274 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5274
               (fun aq  ->
                  let uu____5286 =
                    let uu____5287 =
                      let uu____5288 =
                        let uu____5295 = bv_as_unique_ident x in
                        (uu____5295, aq) in
                      FStar_Parser_AST.PatVar uu____5288 in
                    mk1 uu____5287 in
                  FStar_Pervasives_Native.Some uu____5286))
      | uu____5298 ->
          let uu____5299 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5299
            (fun aq  ->
               let pat =
                 let uu____5314 =
                   let uu____5315 =
                     let uu____5322 = bv_as_unique_ident x in
                     (uu____5322, aq) in
                   FStar_Parser_AST.PatVar uu____5315 in
                 mk1 uu____5314 in
               let uu____5325 = FStar_Options.print_bound_var_types () in
               if uu____5325
               then
                 let uu____5328 =
                   let uu____5329 =
                     let uu____5330 =
                       let uu____5335 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5335) in
                     FStar_Parser_AST.PatAscribed uu____5330 in
                   mk1 uu____5329 in
                 FStar_Pervasives_Native.Some uu____5328
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
              (fun uu____5412  ->
                 match uu____5412 with
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
              (fun uu____5447  ->
                 match uu____5447 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5454 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5454
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5460;
             FStar_Syntax_Syntax.fv_delta = uu____5461;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5488 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5488 FStar_List.rev in
          let args1 =
            let uu____5504 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5524  ->
                      match uu____5524 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5504 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5594 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5594
            | (hd1::tl1,hd2::tl2) ->
                let uu____5617 = map21 tl1 tl2 in (hd1, hd2) :: uu____5617 in
          let args2 =
            let uu____5635 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5635 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5686  ->
                 match uu____5686 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5696 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5696 with
           | FStar_Pervasives_Native.Some (op,uu____5704) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5713 =
                 let uu____5714 =
                   let uu____5721 = bv_as_unique_ident v1 in
                   let uu____5722 = to_arg_qual imp_opt in
                   (uu____5721, uu____5722) in
                 FStar_Parser_AST.PatVar uu____5714 in
               mk1 uu____5713)
      | FStar_Syntax_Syntax.Pat_wild uu____5727 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5735 =
              let uu____5736 =
                let uu____5743 = bv_as_unique_ident bv in
                (uu____5743,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5736 in
            mk1 uu____5735 in
          let uu____5746 = FStar_Options.print_bound_var_types () in
          if uu____5746
          then
            let uu____5747 =
              let uu____5748 =
                let uu____5753 = resugar_term term in (pat, uu____5753) in
              FStar_Parser_AST.PatAscribed uu____5748 in
            mk1 uu____5747
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___243_5759  ->
    match uu___243_5759 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5768 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5769 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5770 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5775 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5784 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5793 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___244_5796  ->
    match uu___244_5796 with
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
          (tylid,uvs,bs,t,uu____5823,datacons) ->
          let uu____5833 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5860,uu____5861,uu____5862,inductive_lid,uu____5864,uu____5865)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5870 -> failwith "unexpected")) in
          (match uu____5833 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5889 = FStar_Options.print_implicits () in
                 if uu____5889 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5899 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___245_5904  ->
                           match uu___245_5904 with
                           | FStar_Syntax_Syntax.RecordType uu____5905 ->
                               true
                           | uu____5914 -> false)) in
                 if uu____5899
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5962,univs1,term,uu____5965,num,uu____5967)
                         ->
                         let uu____5972 =
                           let uu____5973 = FStar_Syntax_Subst.compress term in
                           uu____5973.FStar_Syntax_Syntax.n in
                         (match uu____5972 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5987) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6048  ->
                                        match uu____6048 with
                                        | (b,qual) ->
                                            let uu____6063 =
                                              let uu____6064 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6064 in
                                            let uu____6065 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6063, uu____6065,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6076 -> failwith "unexpected")
                     | uu____6087 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6208,num,uu____6210) ->
                          let c =
                            let uu____6228 =
                              let uu____6231 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6231 in
                            ((l.FStar_Ident.ident), uu____6228,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6248 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6324 ->
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
        let uu____6342 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6342;
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
      let uu____6355 = ts in
      match uu____6355 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6363 =
            let uu____6364 =
              let uu____6377 =
                let uu____6386 =
                  let uu____6393 =
                    let uu____6394 =
                      let uu____6407 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6407) in
                    FStar_Parser_AST.TyconAbbrev uu____6394 in
                  (uu____6393, FStar_Pervasives_Native.None) in
                [uu____6386] in
              (false, uu____6377) in
            FStar_Parser_AST.Tycon uu____6364 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6363
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
            let uu____6461 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6461 with
            | (bs,action_defn) ->
                let uu____6468 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6468 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6476 = FStar_Options.print_implicits () in
                       if uu____6476
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6481 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6481 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6495 =
                           let uu____6506 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6506,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6495 in
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
          let uu____6580 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6580 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6588 = FStar_Options.print_implicits () in
                if uu____6588 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6593 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6593 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6650) ->
        let uu____6659 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6681 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6698 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6705 -> false
                  | uu____6720 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6659 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6752 se1 =
               match uu____6752 with
               | (datacon_ses1,tycons) ->
                   let uu____6778 = resugar_typ datacon_ses1 se1 in
                   (match uu____6778 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6793 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6793 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6828 =
                         let uu____6829 =
                           let uu____6830 =
                             let uu____6843 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6843) in
                           FStar_Parser_AST.Tycon uu____6830 in
                         decl'_to_decl se uu____6829 in
                       FStar_Pervasives_Native.Some uu____6828
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6874,uu____6875,uu____6876,uu____6877,uu____6878)
                            ->
                            let uu____6883 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6883
                        | uu____6886 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6889 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6895) ->
        let uu____6900 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___246_6906  ->
                  match uu___246_6906 with
                  | FStar_Syntax_Syntax.Projector (uu____6907,uu____6908) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6909 -> true
                  | uu____6910 -> false)) in
        if uu____6900
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6933) ->
               let uu____6946 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6946
           | uu____6953 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6957,fml) ->
        let uu____6959 =
          let uu____6960 =
            let uu____6961 =
              let uu____6966 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6966) in
            FStar_Parser_AST.Assume uu____6961 in
          decl'_to_decl se uu____6960 in
        FStar_Pervasives_Native.Some uu____6959
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6968 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6968
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6970 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6970
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6979,t) ->
              let uu____6991 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6991
          | uu____6992 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7000,t) ->
              let uu____7012 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7012
          | uu____7013 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7037 -> failwith "Should not happen hopefully" in
        let uu____7046 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7046
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7056 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7056 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7066 = FStar_Options.print_implicits () in
               if uu____7066 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7075 =
               let uu____7076 =
                 let uu____7077 =
                   let uu____7090 =
                     let uu____7099 =
                       let uu____7106 =
                         let uu____7107 =
                           let uu____7120 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7120) in
                         FStar_Parser_AST.TyconAbbrev uu____7107 in
                       (uu____7106, FStar_Pervasives_Native.None) in
                     [uu____7099] in
                   (false, uu____7090) in
                 FStar_Parser_AST.Tycon uu____7077 in
               decl'_to_decl se uu____7076 in
             FStar_Pervasives_Native.Some uu____7075)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7148 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7148
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7152 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___247_7158  ->
                  match uu___247_7158 with
                  | FStar_Syntax_Syntax.Projector (uu____7159,uu____7160) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7161 -> true
                  | uu____7162 -> false)) in
        if uu____7152
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7167 =
               (let uu____7170 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7170) || (FStar_List.isEmpty uvs) in
             if uu____7167
             then resugar_term t
             else
               (let uu____7172 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7172 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7180 = resugar_term t1 in
                    label universes uu____7180) in
           let uu____7181 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7181)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7182 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7199 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7214 -> FStar_Pervasives_Native.None
