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
      let uu____32 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ()) in
      if uu____32
      then
        let uu____33 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____33
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp:
  'Auu____37 .
    ('Auu____37,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____37,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___101_91  ->
            match uu___101_91 with
            | (uu____98,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____99)) -> false
            | uu____102 -> true))
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
      | uu____177 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____185 = FStar_Options.print_universes () in
    if uu____185
    then
      let uu____186 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____186 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____217 ->
          let uu____218 = universe_to_int (Prims.parse_int "0") u in
          (match uu____218 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____225 =
                      let uu____226 =
                        let uu____227 =
                          let uu____238 = FStar_Util.string_of_int n1 in
                          (uu____238, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____227 in
                      FStar_Parser_AST.Const uu____226 in
                    mk1 uu____225 r
                | uu____249 ->
                    let e1 =
                      let uu____251 =
                        let uu____252 =
                          let uu____253 =
                            let uu____264 = FStar_Util.string_of_int n1 in
                            (uu____264, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____253 in
                        FStar_Parser_AST.Const uu____252 in
                      mk1 uu____251 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____281 ->
               let t =
                 let uu____285 =
                   let uu____286 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____286 in
                 mk1 uu____285 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____292 =
                        let uu____293 =
                          let uu____300 = resugar_universe x r in
                          (acc, uu____300, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____293 in
                      mk1 uu____292 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____302 -> mk1 FStar_Parser_AST.Wild r
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
    let name_of_op uu___102_338 =
      match uu___102_338 with
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
      | uu____429 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____456 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____466 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____466 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____474 ->
               let op =
                 let uu____478 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____512) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____478 in
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
      let uu____698 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____698 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____746 ->
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
                (let uu____799 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____799
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____815 =
      let uu____816 = FStar_Syntax_Subst.compress t in
      uu____816.FStar_Syntax_Syntax.n in
    match uu____815 with
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
        let uu____839 = string_to_op s in
        (match uu____839 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____865 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____878 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____886 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____890 -> true
    | uu____891 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____922 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____922 in
    let var a r =
      let uu____930 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____930 in
    let uu____931 =
      let uu____932 = FStar_Syntax_Subst.compress t in
      uu____932.FStar_Syntax_Syntax.n in
    match uu____931 with
    | FStar_Syntax_Syntax.Tm_delayed uu____935 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____962 = let uu____965 = bv_as_unique_ident x in [uu____965] in
          FStar_Ident.lid_of_ids uu____962 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____968 = let uu____971 = bv_as_unique_ident x in [uu____971] in
          FStar_Ident.lid_of_ids uu____968 in
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
          let uu____989 =
            let uu____990 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____990 in
          mk1 uu____989
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
             | uu____1000 -> failwith "wrong projector format")
          else
            (let uu____1004 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1007 =
                    let uu____1008 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1008 in
                  let uu____1009 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1007 <> uu____1009) in
             if uu____1004
             then
               let uu____1010 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1010
             else
               (let uu____1012 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1012))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1019 = FStar_Options.print_universes () in
        if uu____1019
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1026 =
                   let uu____1027 =
                     let uu____1034 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1034, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1027 in
                 mk1 uu____1026) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1037 = FStar_Syntax_Syntax.is_teff t in
        if uu____1037
        then
          let uu____1038 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1038
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1041 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1041
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1042 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1042
         | uu____1043 ->
             let uu____1044 = FStar_Options.print_universes () in
             if uu____1044
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1062 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1062))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1065) ->
        let uu____1086 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1086 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1094 = FStar_Options.print_implicits () in
               if uu____1094 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1108  ->
                       match uu____1108 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1138 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1138 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1146 = FStar_Options.print_implicits () in
               if uu____1146 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1152 =
                 FStar_All.pipe_right xs2
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1152 FStar_List.rev in
             let rec aux body3 uu___103_1171 =
               match uu___103_1171 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1187 =
          let uu____1192 =
            let uu____1193 = FStar_Syntax_Syntax.mk_binder x in [uu____1193] in
          FStar_Syntax_Subst.open_term uu____1192 phi in
        (match uu____1187 with
         | (x1,phi1) ->
             let b =
               let uu____1197 =
                 let uu____1200 = FStar_List.hd x1 in
                 resugar_binder uu____1200 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1197 in
             let uu____1205 =
               let uu____1206 =
                 let uu____1211 = resugar_term phi1 in (b, uu____1211) in
               FStar_Parser_AST.Refine uu____1206 in
             mk1 uu____1205)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___104_1253 =
          match uu___104_1253 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1323 -> failwith "last of an empty list" in
        let rec last_two uu___105_1359 =
          match uu___105_1359 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1390::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1467::t1 -> last_two t1 in
        let rec last_three uu___106_1508 =
          match uu___106_1508 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1539::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1566::uu____1567::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1675::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1761  ->
                    match uu____1761 with
                    | (e2,qual) ->
                        let uu____1780 = resugar_term e2 in
                        (uu____1780, qual))) in
          let e2 = resugar_term e1 in
          let res_impl desugared_tm qual =
            let uu____1795 = resugar_imp qual in
            match uu____1795 with
            | FStar_Pervasives_Native.Some imp -> imp
            | FStar_Pervasives_Native.None  ->
                ((let uu____1800 =
                    let uu____1805 =
                      let uu____1806 = parser_term_to_string desugared_tm in
                      FStar_Util.format1
                        "Inaccessible argument %s in function application"
                        uu____1806 in
                    (FStar_Errors.InaccessibleArgument, uu____1805) in
                  FStar_Errors.maybe_fatal_error t.FStar_Syntax_Syntax.pos
                    uu____1800);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1819  ->
                 match uu____1819 with
                 | (x,qual) ->
                     let uu____1832 =
                       let uu____1833 =
                         let uu____1840 = res_impl x qual in
                         (acc, x, uu____1840) in
                       FStar_Parser_AST.App uu____1833 in
                     mk1 uu____1832) e2 args2 in
        let args1 =
          let uu____1850 = FStar_Options.print_implicits () in
          if uu____1850 then args else filter_imp args in
        let uu____1862 = resugar_term_as_op e in
        (match uu____1862 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1873) ->
             (match args1 with
              | (fst1,uu____1879)::(snd1,uu____1881)::rest ->
                  let e1 =
                    let uu____1912 =
                      let uu____1913 =
                        let uu____1920 =
                          let uu____1923 = resugar_term fst1 in
                          let uu____1924 =
                            let uu____1927 = resugar_term snd1 in
                            [uu____1927] in
                          uu____1923 :: uu____1924 in
                        ((FStar_Ident.id_of_text "*"), uu____1920) in
                      FStar_Parser_AST.Op uu____1913 in
                    mk1 uu____1912 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1940  ->
                         match uu____1940 with
                         | (x,uu____1946) ->
                             let uu____1947 =
                               let uu____1948 =
                                 let uu____1955 =
                                   let uu____1958 =
                                     let uu____1961 = resugar_term x in
                                     [uu____1961] in
                                   e1 :: uu____1958 in
                                 ((FStar_Ident.id_of_text "*"), uu____1955) in
                               FStar_Parser_AST.Op uu____1948 in
                             mk1 uu____1947) e1 rest
              | uu____1964 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1973) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1999)::[] -> b
               | uu____2016 -> failwith "wrong arguments to dtuple" in
             let uu____2027 =
               let uu____2028 = FStar_Syntax_Subst.compress body in
               uu____2028.FStar_Syntax_Syntax.n in
             (match uu____2027 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2033) ->
                  let uu____2054 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2054 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2062 = FStar_Options.print_implicits () in
                         if uu____2062 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2074 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2095  ->
                            match uu____2095 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2107) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2113) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2118 = FStar_List.hd args1 in
             (match uu____2118 with
              | (t1,uu____2132) ->
                  let uu____2137 =
                    let uu____2138 = FStar_Syntax_Subst.compress t1 in
                    uu____2138.FStar_Syntax_Syntax.n in
                  (match uu____2137 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2143 =
                         let uu____2144 =
                           let uu____2149 = resugar_term t1 in
                           (uu____2149, f) in
                         FStar_Parser_AST.Project uu____2144 in
                       mk1 uu____2143
                   | uu____2150 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2151) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2171 =
               match new_args with
               | (a1,uu____2189)::(a2,uu____2191)::[] -> (a1, a2)
               | uu____2222 -> failwith "wrong arguments to try_with" in
             (match uu____2171 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2253 =
                      let uu____2254 = FStar_Syntax_Subst.compress term in
                      uu____2254.FStar_Syntax_Syntax.n in
                    match uu____2253 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2259) ->
                        let uu____2280 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2280 with | (x1,e2) -> e2)
                    | uu____2287 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2289 = decomp body in resugar_term uu____2289 in
                  let handler1 =
                    let uu____2291 = decomp handler in
                    resugar_term uu____2291 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2297,uu____2298,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2330,uu____2331,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2352 =
                          let uu____2353 =
                            let uu____2362 = resugar_body t11 in
                            (uu____2362, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2353 in
                        mk1 uu____2352
                    | uu____2365 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2420 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2450) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2456) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2541 -> (xs, pat, t1) in
             let resugar body =
               let uu____2552 =
                 let uu____2553 = FStar_Syntax_Subst.compress body in
                 uu____2553.FStar_Syntax_Syntax.n in
               match uu____2552 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2558) ->
                   let uu____2579 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2579 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2587 = FStar_Options.print_implicits () in
                          if uu____2587 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2596 =
                          let uu____2605 =
                            let uu____2606 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2606.FStar_Syntax_Syntax.n in
                          match uu____2605 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2675  ->
                                                 match uu____2675 with
                                                 | (e2,uu____2681) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2684) ->
                                    let uu____2685 =
                                      let uu____2688 =
                                        let uu____2689 = name s r in
                                        mk1 uu____2689 in
                                      [uu____2688] in
                                    [uu____2685]
                                | uu____2694 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2703 ->
                              let uu____2704 = resugar_term body2 in
                              ([], uu____2704) in
                        (match uu____2596 with
                         | (pats,body3) ->
                             let uu____2721 = uncurry xs3 pats body3 in
                             (match uu____2721 with
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
               | uu____2769 ->
                   if op = "forall"
                   then
                     let uu____2770 =
                       let uu____2771 =
                         let uu____2784 = resugar_term body in
                         ([], [[]], uu____2784) in
                       FStar_Parser_AST.QForall uu____2771 in
                     mk1 uu____2770
                   else
                     (let uu____2796 =
                        let uu____2797 =
                          let uu____2810 = resugar_term body in
                          ([], [[]], uu____2810) in
                        FStar_Parser_AST.QExists uu____2797 in
                      mk1 uu____2796) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2837)::[] -> resugar b
                | uu____2854 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2864) ->
             let uu____2869 = FStar_List.hd args1 in
             (match uu____2869 with | (e1,uu____2883) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2928  ->
                       match uu____2928 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____2935 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2935 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2942 =
                         let uu____2943 =
                           let uu____2950 =
                             let uu____2953 = last1 args1 in
                             resugar uu____2953 in
                           (op1, uu____2950) in
                         FStar_Parser_AST.Op uu____2943 in
                       mk1 uu____2942
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2968 =
                         let uu____2969 =
                           let uu____2976 =
                             let uu____2979 = last_two args1 in
                             resugar uu____2979 in
                           (op1, uu____2976) in
                         FStar_Parser_AST.Op uu____2969 in
                       mk1 uu____2968
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2994 =
                         let uu____2995 =
                           let uu____3002 =
                             let uu____3005 = last_three args1 in
                             resugar uu____3005 in
                           (op1, uu____3002) in
                         FStar_Parser_AST.Op uu____2995 in
                       mk1 uu____2994
                   | uu____3014 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3021 =
                    let uu____3022 =
                      let uu____3029 =
                        let uu____3032 = last_two args1 in resugar uu____3032 in
                      (op1, uu____3029) in
                    FStar_Parser_AST.Op uu____3022 in
                  mk1 uu____3021
              | uu____3041 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3044,t1)::[]) ->
        let bnds =
          let uu____3117 =
            let uu____3122 = resugar_pat pat in
            let uu____3123 = resugar_term e in (uu____3122, uu____3123) in
          [uu____3117] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3141,t1)::(pat2,uu____3144,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3240 =
          let uu____3241 =
            let uu____3248 = resugar_term e in
            let uu____3249 = resugar_term t1 in
            let uu____3250 = resugar_term t2 in
            (uu____3248, uu____3249, uu____3250) in
          FStar_Parser_AST.If uu____3241 in
        mk1 uu____3240
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3308 =
          match uu____3308 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3339 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3339 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3343 =
          let uu____3344 =
            let uu____3359 = resugar_term e in
            let uu____3360 = FStar_List.map resugar_branch branches in
            (uu____3359, uu____3360) in
          FStar_Parser_AST.Match uu____3344 in
        mk1 uu____3343
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3400) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3467 =
          let uu____3468 =
            let uu____3477 = resugar_term e in (uu____3477, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3468 in
        mk1 uu____3467
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3501 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3501 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3526 =
                 let uu____3531 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3531 in
               match uu____3526 with
               | (univs1,td) ->
                   let uu____3542 =
                     let uu____3551 =
                       let uu____3552 = FStar_Syntax_Subst.compress td in
                       uu____3552.FStar_Syntax_Syntax.n in
                     match uu____3551 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3563,(t1,uu____3565)::(d,uu____3567)::[]) ->
                         (t1, d)
                     | uu____3610 -> failwith "wrong let binding format" in
                   (match uu____3542 with
                    | (typ,def) ->
                        let uu____3637 =
                          let uu____3644 =
                            let uu____3645 = FStar_Syntax_Subst.compress def in
                            uu____3645.FStar_Syntax_Syntax.n in
                          match uu____3644 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3656) ->
                              let uu____3677 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3677 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3691 =
                                       FStar_Options.print_implicits () in
                                     if uu____3691 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3693 -> ([], def, false) in
                        (match uu____3637 with
                         | (binders,term,is_pat_app) ->
                             let uu____3717 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3728 =
                                     let uu____3729 =
                                       let uu____3730 =
                                         let uu____3737 =
                                           bv_as_unique_ident bv in
                                         (uu____3737,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3730 in
                                     mk_pat uu____3729 in
                                   (uu____3728, term) in
                             (match uu____3717 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3773  ->
                                              match uu____3773 with
                                              | (bv,q) ->
                                                  let uu____3788 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3788
                                                    (fun q1  ->
                                                       let uu____3800 =
                                                         let uu____3801 =
                                                           let uu____3808 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3808, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3801 in
                                                       mk_pat uu____3800))) in
                                    let uu____3811 =
                                      let uu____3816 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3816) in
                                    let uu____3819 =
                                      universe_to_string univs1 in
                                    (uu____3811, uu____3819)
                                  else
                                    (let uu____3825 =
                                       let uu____3830 = resugar_term term1 in
                                       (pat, uu____3830) in
                                     let uu____3831 =
                                       universe_to_string univs1 in
                                     (uu____3825, uu____3831))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3877 =
                   let uu____3878 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3878 in
                 if uu____3877
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___107_3898  ->
                      match uu___107_3898 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3939) ->
        let s =
          let uu____3965 =
            let uu____3966 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3966 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____3965 in
        let uu____3967 = mk1 FStar_Parser_AST.Wild in label s uu____3967
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___108_3977 =
          match uu___108_3977 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____3998 =
                  let uu____3999 = FStar_Syntax_Subst.compress h in
                  uu____3999.FStar_Syntax_Syntax.n in
                match uu____3998 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4019 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4019, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4042 = head_fv_universes_args h1 in
                    (match uu____4042 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4130 = head_fv_universes_args head1 in
                    (match uu____4130 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4202 ->
                    let uu____4203 =
                      let uu____4208 =
                        let uu____4209 =
                          let uu____4210 = resugar_term h in
                          parser_term_to_string uu____4210 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4209 in
                      (FStar_Errors.NotApplicationOrFv, uu____4208) in
                    FStar_Errors.raise_error uu____4203
                      e.FStar_Syntax_Syntax.pos in
              let uu____4227 =
                try
                  let uu____4279 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4279
                with
                | FStar_Errors.Err uu____4300 ->
                    let uu____4305 =
                      let uu____4310 =
                        let uu____4311 =
                          let uu____4312 = resugar_term e in
                          parser_term_to_string uu____4312 in
                        FStar_Util.format1 "wrong Data_app head format %s"
                          uu____4311 in
                      (FStar_Errors.WrongDataAppHeadFormat, uu____4310) in
                    FStar_Errors.raise_error uu____4305
                      e.FStar_Syntax_Syntax.pos in
              (match uu____4227 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4366 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4366, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4390  ->
                          match uu____4390 with
                          | (t1,q) ->
                              let uu____4409 = resugar_imp q in
                              (match uu____4409 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4419 =
                                     let uu____4424 = resugar_term t1 in
                                     (uu____4424, rimp) in
                                   FStar_Pervasives_Native.Some uu____4419
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4440 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4442 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4442) in
                     if uu____4440
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4465,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4490 =
                      let uu____4491 =
                        let uu____4500 = resugar_seq t11 in
                        (uu____4500, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4491 in
                    mk1 uu____4490
                | uu____4503 -> t1 in
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
               | uu____4525 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4527 =
                let uu____4528 = FStar_Syntax_Subst.compress e in
                uu____4528.FStar_Syntax_Syntax.n in
              (match uu____4527 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4532;
                      FStar_Syntax_Syntax.vars = uu____4533;_},(term,uu____4535)::[])
                   -> resugar_term term
               | uu____4564 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4602  ->
                       match uu____4602 with
                       | (x,uu____4608) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4610,p) ->
             let uu____4612 =
               let uu____4613 =
                 let uu____4620 = resugar_term e in (uu____4620, l, p) in
               FStar_Parser_AST.Labeled uu____4613 in
             mk1 uu____4612
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4622,s,uu____4624) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4629 ->
                  (FStar_Errors.maybe_fatal_error e.FStar_Syntax_Syntax.pos
                     (FStar_Errors.MetaAlienNotATmUnknow,
                       "Meta_alien was not a Tm_unknown");
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4638 =
               let uu____4639 =
                 let uu____4648 = resugar_term e in
                 let uu____4649 =
                   let uu____4650 =
                     let uu____4651 =
                       let uu____4662 =
                         let uu____4669 =
                           let uu____4674 = resugar_term t1 in
                           (uu____4674, FStar_Parser_AST.Nothing) in
                         [uu____4669] in
                       (name1, uu____4662) in
                     FStar_Parser_AST.Construct uu____4651 in
                   mk1 uu____4650 in
                 (uu____4648, uu____4649, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4639 in
             mk1 uu____4638
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4692,t1) ->
             let uu____4698 =
               let uu____4699 =
                 let uu____4708 = resugar_term e in
                 let uu____4709 =
                   let uu____4710 =
                     let uu____4711 =
                       let uu____4722 =
                         let uu____4729 =
                           let uu____4734 = resugar_term t1 in
                           (uu____4734, FStar_Parser_AST.Nothing) in
                         [uu____4729] in
                       (name1, uu____4722) in
                     FStar_Parser_AST.Construct uu____4711 in
                   mk1 uu____4710 in
                 (uu____4708, uu____4709, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4699 in
             mk1 uu____4698)
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
             let uu____4782 = FStar_Options.print_universes () in
             if uu____4782
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
             let uu____4843 = FStar_Options.print_universes () in
             if uu____4843
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
          let uu____4884 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4884, FStar_Parser_AST.Nothing) in
        let uu____4885 = FStar_Options.print_effect_args () in
        if uu____4885
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
                    let uu____4972 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____4972, (FStar_Pervasives_Native.snd post)) in
                  let uu____4981 =
                    let uu____4990 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____4990 then [] else [pre] in
                  let uu____5020 =
                    let uu____5029 =
                      let uu____5038 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5038 then [] else [pats] in
                    FStar_List.append [post1] uu____5029 in
                  FStar_List.append uu____4981 uu____5020
              | uu____5092 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5121  ->
                 match uu____5121 with
                 | (e,uu____5131) ->
                     let uu____5132 = resugar_term e in
                     (uu____5132, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___109_5153 =
            match uu___109_5153 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5186 = resugar_term e in
                       (uu____5186, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5191 -> aux l tl1) in
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
      let uu____5236 = b in
      match uu____5236 with
      | (x,aq) ->
          let uu____5241 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5241
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5255 =
                     let uu____5256 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5256 in
                   FStar_Parser_AST.mk_binder uu____5255 r
                     FStar_Parser_AST.Type_level imp
               | uu____5257 ->
                   let uu____5258 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5258
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5260 =
                        let uu____5261 =
                          let uu____5266 = bv_as_unique_ident x in
                          (uu____5266, e) in
                        FStar_Parser_AST.Annotated uu____5261 in
                      FStar_Parser_AST.mk_binder uu____5260 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5275 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5275 in
      let uu____5276 =
        let uu____5277 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5277.FStar_Syntax_Syntax.n in
      match uu____5276 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5285 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5285
          else
            (let uu____5287 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5287
               (fun aq  ->
                  let uu____5299 =
                    let uu____5300 =
                      let uu____5301 =
                        let uu____5308 = bv_as_unique_ident x in
                        (uu____5308, aq) in
                      FStar_Parser_AST.PatVar uu____5301 in
                    mk1 uu____5300 in
                  FStar_Pervasives_Native.Some uu____5299))
      | uu____5311 ->
          let uu____5312 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5312
            (fun aq  ->
               let pat =
                 let uu____5327 =
                   let uu____5328 =
                     let uu____5335 = bv_as_unique_ident x in
                     (uu____5335, aq) in
                   FStar_Parser_AST.PatVar uu____5328 in
                 mk1 uu____5327 in
               let uu____5338 = FStar_Options.print_bound_var_types () in
               if uu____5338
               then
                 let uu____5341 =
                   let uu____5342 =
                     let uu____5343 =
                       let uu____5348 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5348) in
                     FStar_Parser_AST.PatAscribed uu____5343 in
                   mk1 uu____5342 in
                 FStar_Pervasives_Native.Some uu____5341
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
              (fun uu____5425  ->
                 match uu____5425 with
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
              (fun uu____5460  ->
                 match uu____5460 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5467 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5467
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5473;
             FStar_Syntax_Syntax.fv_delta = uu____5474;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5501 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5501 FStar_List.rev in
          let args1 =
            let uu____5517 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5537  ->
                      match uu____5537 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5517 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5607 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5607
            | (hd1::tl1,hd2::tl2) ->
                let uu____5630 = map21 tl1 tl2 in (hd1, hd2) :: uu____5630 in
          let args2 =
            let uu____5648 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5648 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5699  ->
                 match uu____5699 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5709 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5709 with
           | FStar_Pervasives_Native.Some (op,uu____5717) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5726 =
                 let uu____5727 =
                   let uu____5734 = bv_as_unique_ident v1 in
                   let uu____5735 = to_arg_qual imp_opt in
                   (uu____5734, uu____5735) in
                 FStar_Parser_AST.PatVar uu____5727 in
               mk1 uu____5726)
      | FStar_Syntax_Syntax.Pat_wild uu____5740 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5748 =
              let uu____5749 =
                let uu____5756 = bv_as_unique_ident bv in
                (uu____5756,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5749 in
            mk1 uu____5748 in
          let uu____5759 = FStar_Options.print_bound_var_types () in
          if uu____5759
          then
            let uu____5760 =
              let uu____5761 =
                let uu____5766 = resugar_term term in (pat, uu____5766) in
              FStar_Parser_AST.PatAscribed uu____5761 in
            mk1 uu____5760
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___110_5772  ->
    match uu___110_5772 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5781 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5782 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5783 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5788 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5797 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5806 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___111_5809  ->
    match uu___111_5809 with
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
          (tylid,uvs,bs,t,uu____5836,datacons) ->
          let uu____5846 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5873,uu____5874,uu____5875,inductive_lid,uu____5877,uu____5878)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5883 -> failwith "unexpected")) in
          (match uu____5846 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5902 = FStar_Options.print_implicits () in
                 if uu____5902 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5912 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___112_5917  ->
                           match uu___112_5917 with
                           | FStar_Syntax_Syntax.RecordType uu____5918 ->
                               true
                           | uu____5927 -> false)) in
                 if uu____5912
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5975,univs1,term,uu____5978,num,uu____5980)
                         ->
                         let uu____5985 =
                           let uu____5986 = FStar_Syntax_Subst.compress term in
                           uu____5986.FStar_Syntax_Syntax.n in
                         (match uu____5985 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6000) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6061  ->
                                        match uu____6061 with
                                        | (b,qual) ->
                                            let uu____6076 =
                                              let uu____6077 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6077 in
                                            let uu____6078 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6076, uu____6078,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6089 -> failwith "unexpected")
                     | uu____6100 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6221,num,uu____6223) ->
                          let c =
                            let uu____6241 =
                              let uu____6244 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6244 in
                            ((l.FStar_Ident.ident), uu____6241,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6261 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6337 ->
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
        let uu____6355 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6355;
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
      let uu____6368 = ts in
      match uu____6368 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6376 =
            let uu____6377 =
              let uu____6390 =
                let uu____6399 =
                  let uu____6406 =
                    let uu____6407 =
                      let uu____6420 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6420) in
                    FStar_Parser_AST.TyconAbbrev uu____6407 in
                  (uu____6406, FStar_Pervasives_Native.None) in
                [uu____6399] in
              (false, uu____6390) in
            FStar_Parser_AST.Tycon uu____6377 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6376
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
            let uu____6474 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6474 with
            | (bs,action_defn) ->
                let uu____6481 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6481 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6489 = FStar_Options.print_implicits () in
                       if uu____6489
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6494 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6494 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6508 =
                           let uu____6519 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6519,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6508 in
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
          let uu____6593 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6593 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6601 = FStar_Options.print_implicits () in
                if uu____6601 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6606 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6606 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6663) ->
        let uu____6672 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6694 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6711 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6718 -> false
                  | uu____6733 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6672 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6765 se1 =
               match uu____6765 with
               | (datacon_ses1,tycons) ->
                   let uu____6791 = resugar_typ datacon_ses1 se1 in
                   (match uu____6791 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6806 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6806 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6841 =
                         let uu____6842 =
                           let uu____6843 =
                             let uu____6856 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6856) in
                           FStar_Parser_AST.Tycon uu____6843 in
                         decl'_to_decl se uu____6842 in
                       FStar_Pervasives_Native.Some uu____6841
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6887,uu____6888,uu____6889,uu____6890,uu____6891)
                            ->
                            let uu____6896 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6896
                        | uu____6899 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6902 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6908) ->
        let uu____6913 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___113_6919  ->
                  match uu___113_6919 with
                  | FStar_Syntax_Syntax.Projector (uu____6920,uu____6921) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6922 -> true
                  | uu____6923 -> false)) in
        if uu____6913
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6946) ->
               let uu____6959 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6959
           | uu____6966 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6970,fml) ->
        let uu____6972 =
          let uu____6973 =
            let uu____6974 =
              let uu____6979 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6979) in
            FStar_Parser_AST.Assume uu____6974 in
          decl'_to_decl se uu____6973 in
        FStar_Pervasives_Native.Some uu____6972
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6981 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6981
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6983 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6983
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6992,t) ->
              let uu____7004 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7004
          | uu____7005 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7013,t) ->
              let uu____7025 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7025
          | uu____7026 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7050 -> failwith "Should not happen hopefully" in
        let uu____7059 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7059
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
        let uu____7069 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7069 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7079 = FStar_Options.print_implicits () in
               if uu____7079 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7088 =
               let uu____7089 =
                 let uu____7090 =
                   let uu____7103 =
                     let uu____7112 =
                       let uu____7119 =
                         let uu____7120 =
                           let uu____7133 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7133) in
                         FStar_Parser_AST.TyconAbbrev uu____7120 in
                       (uu____7119, FStar_Pervasives_Native.None) in
                     [uu____7112] in
                   (false, uu____7103) in
                 FStar_Parser_AST.Tycon uu____7090 in
               decl'_to_decl se uu____7089 in
             FStar_Pervasives_Native.Some uu____7088)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7161 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7161
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7165 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___114_7171  ->
                  match uu___114_7171 with
                  | FStar_Syntax_Syntax.Projector (uu____7172,uu____7173) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7174 -> true
                  | uu____7175 -> false)) in
        if uu____7165
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7180 =
               (let uu____7183 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7183) || (FStar_List.isEmpty uvs) in
             if uu____7180
             then resugar_term t
             else
               (let uu____7185 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7185 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7193 = resugar_term t1 in
                    label universes uu____7193) in
           let uu____7194 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7194)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7195 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7212 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7227 -> FStar_Pervasives_Native.None