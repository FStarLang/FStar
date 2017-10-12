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
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list
  =
  fun f  ->
    fun l  ->
      let uu____43 =
        FStar_Util.choose_map
          (fun uu____53  -> fun x  -> let uu____55 = f x in ((), uu____55))
          () l in
      FStar_Pervasives_Native.snd uu____43
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____67 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____67
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp:
  'Auu____73 .
    ('Auu____73,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____73,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___186_127  ->
            match uu___186_127 with
            | (uu____134,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____135)) -> false
            | uu____138 -> true))
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
      | uu____213 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____222 = FStar_Options.print_universes () in
    if uu____222
    then
      let uu____223 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____223 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____256 ->
          let uu____257 = universe_to_int (Prims.parse_int "0") u in
          (match uu____257 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____264 =
                      let uu____265 =
                        let uu____266 =
                          let uu____277 = FStar_Util.string_of_int n1 in
                          (uu____277, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____266 in
                      FStar_Parser_AST.Const uu____265 in
                    mk1 uu____264 r
                | uu____288 ->
                    let e1 =
                      let uu____290 =
                        let uu____291 =
                          let uu____292 =
                            let uu____303 = FStar_Util.string_of_int n1 in
                            (uu____303, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____292 in
                        FStar_Parser_AST.Const uu____291 in
                      mk1 uu____290 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____320 ->
               let t =
                 let uu____324 =
                   let uu____325 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____325 in
                 mk1 uu____324 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____331 =
                        let uu____332 =
                          let uu____339 = resugar_universe x r in
                          (acc, uu____339, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____332 in
                      mk1 uu____331 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____341 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____352 =
              let uu____357 =
                let uu____358 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____358 in
              (uu____357, r) in
            FStar_Ident.mk_ident uu____352 in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___187_378 =
      match uu___187_378 with
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
      | uu____469 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____496 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____506 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____506 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____514 ->
               let op =
                 let uu____518 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____552) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____518 in
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
      let uu____739 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____739 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____787 ->
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
                (let uu____840 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____840
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____856 =
      let uu____857 = FStar_Syntax_Subst.compress t in
      uu____857.FStar_Syntax_Syntax.n in
    match uu____856 with
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
        let uu____880 = string_to_op s in
        (match uu____880 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____906 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____919 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____928 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____933 -> true
    | uu____934 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____965 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____965 in
    let var a r =
      let uu____973 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____973 in
    let uu____974 =
      let uu____975 = FStar_Syntax_Subst.compress t in
      uu____975.FStar_Syntax_Syntax.n in
    match uu____974 with
    | FStar_Syntax_Syntax.Tm_delayed uu____978 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____1005 =
            let uu____1008 = bv_as_unique_ident x in [uu____1008] in
          FStar_Ident.lid_of_ids uu____1005 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____1011 =
            let uu____1014 = bv_as_unique_ident x in [uu____1014] in
          FStar_Ident.lid_of_ids uu____1011 in
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
          let uu____1032 =
            let uu____1033 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____1033 in
          mk1 uu____1032
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
             | uu____1043 -> failwith "wrong projector format")
          else
            (let uu____1047 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1050 =
                    let uu____1051 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1051 in
                  let uu____1061 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1050 <> uu____1061) in
             if uu____1047
             then
               let uu____1074 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1074
             else
               (let uu____1076 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1076))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1083 = FStar_Options.print_universes () in
        if uu____1083
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1090 =
                   let uu____1091 =
                     let uu____1098 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1098, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1091 in
                 mk1 uu____1090) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1101 = FStar_Syntax_Syntax.is_teff t in
        if uu____1101
        then
          let uu____1102 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1102
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1105 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1105
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1106 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1106
         | uu____1107 ->
             let uu____1108 = FStar_Options.print_universes () in
             if uu____1108
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1126 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1126))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1129) ->
        let uu____1150 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1150 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1158 = FStar_Options.print_implicits () in
               if uu____1158 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1172  ->
                       match uu____1172 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1202 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1202 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1210 = FStar_Options.print_implicits () in
               if uu____1210 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1216 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1216 FStar_List.rev in
             let rec aux body3 uu___188_1235 =
               match uu___188_1235 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1251 =
          let uu____1256 =
            let uu____1257 = FStar_Syntax_Syntax.mk_binder x in [uu____1257] in
          FStar_Syntax_Subst.open_term uu____1256 phi in
        (match uu____1251 with
         | (x1,phi1) ->
             let b =
               let uu____1261 =
                 let uu____1264 = FStar_List.hd x1 in
                 resugar_binder uu____1264 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1261 in
             let uu____1269 =
               let uu____1270 =
                 let uu____1275 = resugar_term phi1 in (b, uu____1275) in
               FStar_Parser_AST.Refine uu____1270 in
             mk1 uu____1269)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___189_1317 =
          match uu___189_1317 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1387 -> failwith "last of an empty list" in
        let rec last_two uu___190_1423 =
          match uu___190_1423 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1454::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1531::t1 -> last_two t1 in
        let rec last_three uu___191_1572 =
          match uu___191_1572 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1603::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1630::uu____1631::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1739::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1825  ->
                    match uu____1825 with
                    | (e2,qual) ->
                        let uu____1844 = resugar_term e2 in
                        (uu____1844, qual))) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1860  ->
                 match uu____1860 with
                 | (x,qual) ->
                     let uu____1873 =
                       let uu____1874 =
                         let uu____1881 = resugar_imp qual in
                         (acc, x, uu____1881) in
                       FStar_Parser_AST.App uu____1874 in
                     mk1 uu____1873) e2 args2 in
        let args1 =
          let uu____1891 = FStar_Options.print_implicits () in
          if uu____1891 then args else filter_imp args in
        let uu____1903 = resugar_term_as_op e in
        (match uu____1903 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1914) ->
             (match args1 with
              | (fst1,uu____1920)::(snd1,uu____1922)::rest ->
                  let e1 =
                    let uu____1953 =
                      let uu____1954 =
                        let uu____1961 =
                          let uu____1964 = resugar_term fst1 in
                          let uu____1965 =
                            let uu____1968 = resugar_term snd1 in
                            [uu____1968] in
                          uu____1964 :: uu____1965 in
                        ((FStar_Ident.id_of_text "*"), uu____1961) in
                      FStar_Parser_AST.Op uu____1954 in
                    mk1 uu____1953 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1981  ->
                         match uu____1981 with
                         | (x,uu____1987) ->
                             let uu____1988 =
                               let uu____1989 =
                                 let uu____1996 =
                                   let uu____1999 =
                                     let uu____2002 = resugar_term x in
                                     [uu____2002] in
                                   e1 :: uu____1999 in
                                 ((FStar_Ident.id_of_text "*"), uu____1996) in
                               FStar_Parser_AST.Op uu____1989 in
                             mk1 uu____1988) e1 rest
              | uu____2005 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2014) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2040)::[] -> b
               | uu____2057 -> failwith "wrong arguments to dtuple" in
             let uu____2068 =
               let uu____2069 = FStar_Syntax_Subst.compress body in
               uu____2069.FStar_Syntax_Syntax.n in
             (match uu____2068 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2074) ->
                  let uu____2095 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2095 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2103 = FStar_Options.print_implicits () in
                         if uu____2103 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2115 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2136  ->
                            match uu____2136 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2148) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2154) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2159 = FStar_List.hd args1 in
             (match uu____2159 with
              | (t1,uu____2173) ->
                  let uu____2178 =
                    let uu____2179 = FStar_Syntax_Subst.compress t1 in
                    uu____2179.FStar_Syntax_Syntax.n in
                  (match uu____2178 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2184 =
                         let uu____2185 =
                           let uu____2190 = resugar_term t1 in
                           (uu____2190, f) in
                         FStar_Parser_AST.Project uu____2185 in
                       mk1 uu____2184
                   | uu____2191 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2192) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2212 =
               match new_args with
               | (a1,uu____2230)::(a2,uu____2232)::[] -> (a1, a2)
               | uu____2263 -> failwith "wrong arguments to try_with" in
             (match uu____2212 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2294 =
                      let uu____2295 = FStar_Syntax_Subst.compress term in
                      uu____2295.FStar_Syntax_Syntax.n in
                    match uu____2294 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2300) ->
                        let uu____2321 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2321 with | (x1,e2) -> e2)
                    | uu____2328 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2330 = decomp body in resugar_term uu____2330 in
                  let handler1 =
                    let uu____2332 = decomp handler in
                    resugar_term uu____2332 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2338,uu____2339,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2371,uu____2372,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2393 =
                          let uu____2394 =
                            let uu____2403 = resugar_body t11 in
                            (uu____2403, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2394 in
                        mk1 uu____2393
                    | uu____2406 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2461 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2491) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2497) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2582 -> (xs, pat, t1) in
             let resugar body =
               let uu____2593 =
                 let uu____2594 = FStar_Syntax_Subst.compress body in
                 uu____2594.FStar_Syntax_Syntax.n in
               match uu____2593 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2599) ->
                   let uu____2620 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2620 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2628 = FStar_Options.print_implicits () in
                          if uu____2628 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2637 =
                          let uu____2646 =
                            let uu____2647 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2647.FStar_Syntax_Syntax.n in
                          match uu____2646 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2716  ->
                                                 match uu____2716 with
                                                 | (e2,uu____2722) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2725) ->
                                    let uu____2726 =
                                      let uu____2729 =
                                        let uu____2730 = name s r in
                                        mk1 uu____2730 in
                                      [uu____2729] in
                                    [uu____2726]
                                | uu____2735 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2744 ->
                              let uu____2745 = resugar_term body2 in
                              ([], uu____2745) in
                        (match uu____2637 with
                         | (pats,body3) ->
                             let uu____2762 = uncurry xs3 pats body3 in
                             (match uu____2762 with
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
               | uu____2810 ->
                   if op = "forall"
                   then
                     let uu____2811 =
                       let uu____2812 =
                         let uu____2825 = resugar_term body in
                         ([], [[]], uu____2825) in
                       FStar_Parser_AST.QForall uu____2812 in
                     mk1 uu____2811
                   else
                     (let uu____2837 =
                        let uu____2838 =
                          let uu____2851 = resugar_term body in
                          ([], [[]], uu____2851) in
                        FStar_Parser_AST.QExists uu____2838 in
                      mk1 uu____2837) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2878)::[] -> resugar b
                | uu____2895 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2905) ->
             let uu____2910 = FStar_List.hd args1 in
             (match uu____2910 with | (e1,uu____2924) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2969  ->
                       match uu____2969 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_40 when _0_40 = (Prims.parse_int "0") ->
                  let uu____2976 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2976 with
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2983 =
                         let uu____2984 =
                           let uu____2991 =
                             let uu____2994 = last1 args1 in
                             resugar uu____2994 in
                           (op1, uu____2991) in
                         FStar_Parser_AST.Op uu____2984 in
                       mk1 uu____2983
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____3009 =
                         let uu____3010 =
                           let uu____3017 =
                             let uu____3020 = last_two args1 in
                             resugar uu____3020 in
                           (op1, uu____3017) in
                         FStar_Parser_AST.Op uu____3010 in
                       mk1 uu____3009
                   | _0_43 when
                       (_0_43 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3035 =
                         let uu____3036 =
                           let uu____3043 =
                             let uu____3046 = last_three args1 in
                             resugar uu____3046 in
                           (op1, uu____3043) in
                         FStar_Parser_AST.Op uu____3036 in
                       mk1 uu____3035
                   | uu____3055 -> resugar_as_app e args1)
              | _0_44 when
                  (_0_44 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3062 =
                    let uu____3063 =
                      let uu____3070 =
                        let uu____3073 = last_two args1 in resugar uu____3073 in
                      (op1, uu____3070) in
                    FStar_Parser_AST.Op uu____3063 in
                  mk1 uu____3062
              | uu____3082 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3085,t1)::[]) ->
        let bnds =
          let uu____3158 =
            let uu____3163 = resugar_pat pat in
            let uu____3164 = resugar_term e in (uu____3163, uu____3164) in
          [uu____3158] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3182,t1)::(pat2,uu____3185,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3281 =
          let uu____3282 =
            let uu____3289 = resugar_term e in
            let uu____3290 = resugar_term t1 in
            let uu____3291 = resugar_term t2 in
            (uu____3289, uu____3290, uu____3291) in
          FStar_Parser_AST.If uu____3282 in
        mk1 uu____3281
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3349 =
          match uu____3349 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3380 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3380 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3384 =
          let uu____3385 =
            let uu____3400 = resugar_term e in
            let uu____3401 = FStar_List.map resugar_branch branches in
            (uu____3400, uu____3401) in
          FStar_Parser_AST.Match uu____3385 in
        mk1 uu____3384
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3441) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3508 =
          let uu____3509 =
            let uu____3518 = resugar_term e in (uu____3518, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3509 in
        mk1 uu____3508
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3542 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3542 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3567 =
                 let uu____3572 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3572 in
               match uu____3567 with
               | (univs1,td) ->
                   let uu____3583 =
                     let uu____3592 =
                       let uu____3593 = FStar_Syntax_Subst.compress td in
                       uu____3593.FStar_Syntax_Syntax.n in
                     match uu____3592 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3604,(t1,uu____3606)::(d,uu____3608)::[]) ->
                         (t1, d)
                     | uu____3651 -> failwith "wrong let binding format" in
                   (match uu____3583 with
                    | (typ,def) ->
                        let uu____3678 =
                          let uu____3685 =
                            let uu____3686 = FStar_Syntax_Subst.compress def in
                            uu____3686.FStar_Syntax_Syntax.n in
                          match uu____3685 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3697) ->
                              let uu____3718 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3718 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3732 =
                                       FStar_Options.print_implicits () in
                                     if uu____3732 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3734 -> ([], def, false) in
                        (match uu____3678 with
                         | (binders,term,is_pat_app) ->
                             let uu____3758 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3769 =
                                     let uu____3770 =
                                       let uu____3771 =
                                         let uu____3778 =
                                           bv_as_unique_ident bv in
                                         (uu____3778,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3771 in
                                     mk_pat uu____3770 in
                                   (uu____3769, term) in
                             (match uu____3758 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____3814  ->
                                              match uu____3814 with
                                              | (bv,q) ->
                                                  let uu____3829 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3829
                                                    (fun q1  ->
                                                       let uu____3841 =
                                                         let uu____3842 =
                                                           let uu____3849 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3849, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3842 in
                                                       mk_pat uu____3841))) in
                                    let uu____3852 =
                                      let uu____3857 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3857) in
                                    let uu____3860 =
                                      universe_to_string univs1 in
                                    (uu____3852, uu____3860)
                                  else
                                    (let uu____3866 =
                                       let uu____3871 = resugar_term term1 in
                                       (pat, uu____3871) in
                                     let uu____3872 =
                                       universe_to_string univs1 in
                                     (uu____3866, uu____3872))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3918 =
                   let uu____3919 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3919 in
                 if uu____3918
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___192_3939  ->
                      match uu___192_3939 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3980) ->
        let s =
          let uu____4006 =
            let uu____4007 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____4007 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____4006 in
        let uu____4008 = mk1 FStar_Parser_AST.Wild in label s uu____4008
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___193_4018 =
          match uu___193_4018 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4039 =
                  let uu____4040 = FStar_Syntax_Subst.compress h in
                  uu____4040.FStar_Syntax_Syntax.n in
                match uu____4039 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4060 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4060, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4083 = head_fv_universes_args h1 in
                    (match uu____4083 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4171 = head_fv_universes_args head1 in
                    (match uu____4171 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4243 ->
                    let uu____4244 =
                      let uu____4245 =
                        let uu____4246 =
                          let uu____4247 = resugar_term h in
                          parser_term_to_string uu____4247 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4246 in
                      FStar_Errors.Err uu____4245 in
                    FStar_Exn.raise uu____4244 in
              let uu____4264 =
                try
                  let uu____4316 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4316
                with
                | FStar_Errors.Err uu____4337 ->
                    let uu____4338 =
                      let uu____4339 =
                        let uu____4344 =
                          let uu____4345 =
                            let uu____4346 = resugar_term e in
                            parser_term_to_string uu____4346 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4345 in
                        (uu____4344, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4339 in
                    FStar_Exn.raise uu____4338 in
              (match uu____4264 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4400 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4400, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.map
                       (fun uu____4423  ->
                          match uu____4423 with
                          | (t1,q) ->
                              let uu____4440 = resugar_term t1 in
                              let uu____4441 = resugar_imp q in
                              (uu____4440, uu____4441)) args in
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
         | FStar_Syntax_Syntax.Meta_alien (uu____4631,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4640 =
               let uu____4641 =
                 let uu____4650 = resugar_term e in
                 let uu____4651 =
                   let uu____4652 =
                     let uu____4653 =
                       let uu____4664 =
                         let uu____4671 =
                           let uu____4676 = resugar_term t1 in
                           (uu____4676, FStar_Parser_AST.Nothing) in
                         [uu____4671] in
                       (name1, uu____4664) in
                     FStar_Parser_AST.Construct uu____4653 in
                   mk1 uu____4652 in
                 (uu____4650, uu____4651, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4641 in
             mk1 uu____4640
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4694,t1) ->
             let uu____4700 =
               let uu____4701 =
                 let uu____4710 = resugar_term e in
                 let uu____4711 =
                   let uu____4712 =
                     let uu____4713 =
                       let uu____4724 =
                         let uu____4731 =
                           let uu____4736 = resugar_term t1 in
                           (uu____4736, FStar_Parser_AST.Nothing) in
                         [uu____4731] in
                       (name1, uu____4724) in
                     FStar_Parser_AST.Construct uu____4713 in
                   mk1 uu____4712 in
                 (uu____4710, uu____4711, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4701 in
             mk1 uu____4700)
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
             let uu____4784 = FStar_Options.print_universes () in
             if uu____4784
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
             let uu____4845 = FStar_Options.print_universes () in
             if uu____4845
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
          let uu____4886 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4886, FStar_Parser_AST.Nothing) in
        let uu____4887 = FStar_Options.print_effect_args () in
        if uu____4887
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___194_4944 =
                match uu___194_4944 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____5005 -> aux l tl1
                     | uu____5012 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5047  ->
                 match uu____5047 with
                 | (e,uu____5057) ->
                     let uu____5058 = resugar_term e in
                     (uu____5058, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___195_5079 =
            match uu___195_5079 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5112 = resugar_term e in
                       (uu____5112, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5117 -> aux l tl1) in
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
      let uu____5162 = b in
      match uu____5162 with
      | (x,aq) ->
          let uu____5167 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5167
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5181 =
                     let uu____5182 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5182 in
                   FStar_Parser_AST.mk_binder uu____5181 r
                     FStar_Parser_AST.Type_level imp
               | uu____5183 ->
                   let uu____5184 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5184
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5186 =
                        let uu____5187 =
                          let uu____5192 = bv_as_unique_ident x in
                          (uu____5192, e) in
                        FStar_Parser_AST.Annotated uu____5187 in
                      FStar_Parser_AST.mk_binder uu____5186 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5201 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5201 in
      let uu____5202 =
        let uu____5203 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5203.FStar_Syntax_Syntax.n in
      match uu____5202 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5211 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5211
          else
            (let uu____5213 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5213
               (fun aq  ->
                  let uu____5225 =
                    let uu____5226 =
                      let uu____5227 =
                        let uu____5234 = bv_as_unique_ident x in
                        (uu____5234, aq) in
                      FStar_Parser_AST.PatVar uu____5227 in
                    mk1 uu____5226 in
                  FStar_Pervasives_Native.Some uu____5225))
      | uu____5237 ->
          let uu____5238 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5238
            (fun aq  ->
               let pat =
                 let uu____5253 =
                   let uu____5254 =
                     let uu____5261 = bv_as_unique_ident x in
                     (uu____5261, aq) in
                   FStar_Parser_AST.PatVar uu____5254 in
                 mk1 uu____5253 in
               let uu____5264 = FStar_Options.print_bound_var_types () in
               if uu____5264
               then
                 let uu____5267 =
                   let uu____5268 =
                     let uu____5269 =
                       let uu____5274 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5274) in
                     FStar_Parser_AST.PatAscribed uu____5269 in
                   mk1 uu____5268 in
                 FStar_Pervasives_Native.Some uu____5267
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
              (fun uu____5351  ->
                 match uu____5351 with
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
              (fun uu____5386  ->
                 match uu____5386 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5393 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5393
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5399;
             FStar_Syntax_Syntax.fv_delta = uu____5400;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5427 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5427 FStar_List.rev in
          let args1 =
            let uu____5443 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5463  ->
                      match uu____5463 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5443 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5533 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5533
            | (hd1::tl1,hd2::tl2) ->
                let uu____5556 = map21 tl1 tl2 in (hd1, hd2) :: uu____5556 in
          let args2 =
            let uu____5574 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5574 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5625  ->
                 match uu____5625 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5635 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5635 with
           | FStar_Pervasives_Native.Some (op,uu____5643) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5652 =
                 let uu____5653 =
                   let uu____5660 = bv_as_unique_ident v1 in
                   let uu____5661 = to_arg_qual imp_opt in
                   (uu____5660, uu____5661) in
                 FStar_Parser_AST.PatVar uu____5653 in
               mk1 uu____5652)
      | FStar_Syntax_Syntax.Pat_wild uu____5666 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5674 =
              let uu____5675 =
                let uu____5682 = bv_as_unique_ident bv in
                (uu____5682,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5675 in
            mk1 uu____5674 in
          let uu____5685 = FStar_Options.print_bound_var_types () in
          if uu____5685
          then
            let uu____5686 =
              let uu____5687 =
                let uu____5692 = resugar_term term in (pat, uu____5692) in
              FStar_Parser_AST.PatAscribed uu____5687 in
            mk1 uu____5686
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___196_5699  ->
    match uu___196_5699 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5708 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5709 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5710 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5715 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5724 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5733 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___197_5737  ->
    match uu___197_5737 with
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
          (tylid,uvs,bs,t,uu____5766,datacons) ->
          let uu____5776 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5803,uu____5804,uu____5805,inductive_lid,uu____5807,uu____5808)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5813 -> failwith "unexpected")) in
          (match uu____5776 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5832 = FStar_Options.print_implicits () in
                 if uu____5832 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5842 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___198_5847  ->
                           match uu___198_5847 with
                           | FStar_Syntax_Syntax.RecordType uu____5848 ->
                               true
                           | uu____5857 -> false)) in
                 if uu____5842
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5905,univs1,term,uu____5908,num,uu____5910)
                         ->
                         let uu____5915 =
                           let uu____5916 = FStar_Syntax_Subst.compress term in
                           uu____5916.FStar_Syntax_Syntax.n in
                         (match uu____5915 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5930) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____5991  ->
                                        match uu____5991 with
                                        | (b,qual) ->
                                            let uu____6006 =
                                              let uu____6007 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6007 in
                                            let uu____6008 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6006, uu____6008,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6019 -> failwith "unexpected")
                     | uu____6030 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6151,num,uu____6153) ->
                          let c =
                            let uu____6171 =
                              let uu____6174 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6174 in
                            ((l.FStar_Ident.ident), uu____6171,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6191 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6267 ->
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
        let uu____6288 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6288;
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
      let uu____6305 = ts in
      match uu____6305 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6313 =
            let uu____6314 =
              let uu____6327 =
                let uu____6336 =
                  let uu____6343 =
                    let uu____6344 =
                      let uu____6357 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6357) in
                    FStar_Parser_AST.TyconAbbrev uu____6344 in
                  (uu____6343, FStar_Pervasives_Native.None) in
                [uu____6336] in
              (false, uu____6327) in
            FStar_Parser_AST.Tycon uu____6314 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6313
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
            let uu____6416 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6416 with
            | (bs,action_defn) ->
                let uu____6423 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6423 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6431 = FStar_Options.print_implicits () in
                       if uu____6431
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6436 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6436 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6450 =
                           let uu____6461 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6461,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6450 in
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
          let uu____6535 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6535 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6543 = FStar_Options.print_implicits () in
                if uu____6543 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6548 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6548 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6606) ->
        let uu____6615 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6637 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6654 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6661 -> false
                  | uu____6676 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6615 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6708 se1 =
               match uu____6708 with
               | (datacon_ses1,tycons) ->
                   let uu____6734 = resugar_typ datacon_ses1 se1 in
                   (match uu____6734 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6749 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6749 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6784 =
                         let uu____6785 =
                           let uu____6786 =
                             let uu____6799 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6799) in
                           FStar_Parser_AST.Tycon uu____6786 in
                         decl'_to_decl se uu____6785 in
                       FStar_Pervasives_Native.Some uu____6784
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6830,uu____6831,uu____6832,uu____6833,uu____6834)
                            ->
                            let uu____6839 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6839
                        | uu____6842 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6845 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6851) ->
        let uu____6856 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___199_6862  ->
                  match uu___199_6862 with
                  | FStar_Syntax_Syntax.Projector (uu____6863,uu____6864) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6865 -> true
                  | uu____6866 -> false)) in
        if uu____6856
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6889) ->
               let uu____6902 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6902
           | uu____6909 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6913,fml) ->
        let uu____6915 =
          let uu____6916 =
            let uu____6917 =
              let uu____6922 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6922) in
            FStar_Parser_AST.Assume uu____6917 in
          decl'_to_decl se uu____6916 in
        FStar_Pervasives_Native.Some uu____6915
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6924 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6924
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6926 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6926
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6935,t) ->
              let uu____6947 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6947
          | uu____6948 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____6956,t) ->
              let uu____6968 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6968
          | uu____6969 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____6993 -> failwith "Should not happen hopefully" in
        let uu____7002 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7002
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7012 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7012 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7022 = FStar_Options.print_implicits () in
               if uu____7022 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7031 =
               let uu____7032 =
                 let uu____7033 =
                   let uu____7046 =
                     let uu____7055 =
                       let uu____7062 =
                         let uu____7063 =
                           let uu____7076 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7076) in
                         FStar_Parser_AST.TyconAbbrev uu____7063 in
                       (uu____7062, FStar_Pervasives_Native.None) in
                     [uu____7055] in
                   (false, uu____7046) in
                 FStar_Parser_AST.Tycon uu____7033 in
               decl'_to_decl se uu____7032 in
             FStar_Pervasives_Native.Some uu____7031)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7104 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7104
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7108 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___200_7114  ->
                  match uu___200_7114 with
                  | FStar_Syntax_Syntax.Projector (uu____7115,uu____7116) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7117 -> true
                  | uu____7118 -> false)) in
        if uu____7108
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7123 =
               (let uu____7126 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7126) || (FStar_List.isEmpty uvs) in
             if uu____7123
             then resugar_term t
             else
               (let uu____7128 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7128 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7136 = resugar_term t1 in
                    label universes uu____7136) in
           let uu____7137 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7137)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7138 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7155 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7170 -> FStar_Pervasives_Native.None