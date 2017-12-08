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
         (fun uu___234_91  ->
            match uu___234_91 with
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
    let name_of_op uu___235_338 =
      match uu___235_338 with
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
             let rec aux body3 uu___236_1171 =
               match uu___236_1171 with
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
        let rec last1 uu___237_1253 =
          match uu___237_1253 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1323 -> failwith "last of an empty list" in
        let rec last_two uu___238_1359 =
          match uu___238_1359 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1390::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1467::t1 -> last_two t1 in
        let rec last_three uu___239_1508 =
          match uu___239_1508 with
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
                    let uu____1801 = parser_term_to_string desugared_tm in
                    FStar_Util.format1
                      "Inaccessible argument %s in function application"
                      uu____1801 in
                  FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1800);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1814  ->
                 match uu____1814 with
                 | (x,qual) ->
                     let uu____1827 =
                       let uu____1828 =
                         let uu____1835 = res_impl x qual in
                         (acc, x, uu____1835) in
                       FStar_Parser_AST.App uu____1828 in
                     mk1 uu____1827) e2 args2 in
        let args1 =
          let uu____1845 = FStar_Options.print_implicits () in
          if uu____1845 then args else filter_imp args in
        let uu____1857 = resugar_term_as_op e in
        (match uu____1857 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1868) ->
             (match args1 with
              | (fst1,uu____1874)::(snd1,uu____1876)::rest ->
                  let e1 =
                    let uu____1907 =
                      let uu____1908 =
                        let uu____1915 =
                          let uu____1918 = resugar_term fst1 in
                          let uu____1919 =
                            let uu____1922 = resugar_term snd1 in
                            [uu____1922] in
                          uu____1918 :: uu____1919 in
                        ((FStar_Ident.id_of_text "*"), uu____1915) in
                      FStar_Parser_AST.Op uu____1908 in
                    mk1 uu____1907 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1935  ->
                         match uu____1935 with
                         | (x,uu____1941) ->
                             let uu____1942 =
                               let uu____1943 =
                                 let uu____1950 =
                                   let uu____1953 =
                                     let uu____1956 = resugar_term x in
                                     [uu____1956] in
                                   e1 :: uu____1953 in
                                 ((FStar_Ident.id_of_text "*"), uu____1950) in
                               FStar_Parser_AST.Op uu____1943 in
                             mk1 uu____1942) e1 rest
              | uu____1959 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1968) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1994)::[] -> b
               | uu____2011 -> failwith "wrong arguments to dtuple" in
             let uu____2022 =
               let uu____2023 = FStar_Syntax_Subst.compress body in
               uu____2023.FStar_Syntax_Syntax.n in
             (match uu____2022 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2028) ->
                  let uu____2049 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2049 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2057 = FStar_Options.print_implicits () in
                         if uu____2057 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2069 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2090  ->
                            match uu____2090 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2102) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2108) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2113 = FStar_List.hd args1 in
             (match uu____2113 with
              | (t1,uu____2127) ->
                  let uu____2132 =
                    let uu____2133 = FStar_Syntax_Subst.compress t1 in
                    uu____2133.FStar_Syntax_Syntax.n in
                  (match uu____2132 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2138 =
                         let uu____2139 =
                           let uu____2144 = resugar_term t1 in
                           (uu____2144, f) in
                         FStar_Parser_AST.Project uu____2139 in
                       mk1 uu____2138
                   | uu____2145 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2146) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2166 =
               match new_args with
               | (a1,uu____2184)::(a2,uu____2186)::[] -> (a1, a2)
               | uu____2217 -> failwith "wrong arguments to try_with" in
             (match uu____2166 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2248 =
                      let uu____2249 = FStar_Syntax_Subst.compress term in
                      uu____2249.FStar_Syntax_Syntax.n in
                    match uu____2248 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2254) ->
                        let uu____2275 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2275 with | (x1,e2) -> e2)
                    | uu____2282 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2284 = decomp body in resugar_term uu____2284 in
                  let handler1 =
                    let uu____2286 = decomp handler in
                    resugar_term uu____2286 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2292,uu____2293,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2325,uu____2326,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2347 =
                          let uu____2348 =
                            let uu____2357 = resugar_body t11 in
                            (uu____2357, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2348 in
                        mk1 uu____2347
                    | uu____2360 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2415 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2445) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2451) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2536 -> (xs, pat, t1) in
             let resugar body =
               let uu____2547 =
                 let uu____2548 = FStar_Syntax_Subst.compress body in
                 uu____2548.FStar_Syntax_Syntax.n in
               match uu____2547 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2553) ->
                   let uu____2574 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2574 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2582 = FStar_Options.print_implicits () in
                          if uu____2582 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2591 =
                          let uu____2600 =
                            let uu____2601 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2601.FStar_Syntax_Syntax.n in
                          match uu____2600 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2670  ->
                                                 match uu____2670 with
                                                 | (e2,uu____2676) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2679) ->
                                    let uu____2680 =
                                      let uu____2683 =
                                        let uu____2684 = name s r in
                                        mk1 uu____2684 in
                                      [uu____2683] in
                                    [uu____2680]
                                | uu____2689 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2698 ->
                              let uu____2699 = resugar_term body2 in
                              ([], uu____2699) in
                        (match uu____2591 with
                         | (pats,body3) ->
                             let uu____2716 = uncurry xs3 pats body3 in
                             (match uu____2716 with
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
               | uu____2764 ->
                   if op = "forall"
                   then
                     let uu____2765 =
                       let uu____2766 =
                         let uu____2779 = resugar_term body in
                         ([], [[]], uu____2779) in
                       FStar_Parser_AST.QForall uu____2766 in
                     mk1 uu____2765
                   else
                     (let uu____2791 =
                        let uu____2792 =
                          let uu____2805 = resugar_term body in
                          ([], [[]], uu____2805) in
                        FStar_Parser_AST.QExists uu____2792 in
                      mk1 uu____2791) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2832)::[] -> resugar b
                | uu____2849 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2859) ->
             let uu____2864 = FStar_List.hd args1 in
             (match uu____2864 with | (e1,uu____2878) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2923  ->
                       match uu____2923 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____2930 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2930 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2937 =
                         let uu____2938 =
                           let uu____2945 =
                             let uu____2948 = last1 args1 in
                             resugar uu____2948 in
                           (op1, uu____2945) in
                         FStar_Parser_AST.Op uu____2938 in
                       mk1 uu____2937
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2963 =
                         let uu____2964 =
                           let uu____2971 =
                             let uu____2974 = last_two args1 in
                             resugar uu____2974 in
                           (op1, uu____2971) in
                         FStar_Parser_AST.Op uu____2964 in
                       mk1 uu____2963
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2989 =
                         let uu____2990 =
                           let uu____2997 =
                             let uu____3000 = last_three args1 in
                             resugar uu____3000 in
                           (op1, uu____2997) in
                         FStar_Parser_AST.Op uu____2990 in
                       mk1 uu____2989
                   | uu____3009 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3016 =
                    let uu____3017 =
                      let uu____3024 =
                        let uu____3027 = last_two args1 in resugar uu____3027 in
                      (op1, uu____3024) in
                    FStar_Parser_AST.Op uu____3017 in
                  mk1 uu____3016
              | uu____3036 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3039,t1)::[]) ->
        let bnds =
          let uu____3112 =
            let uu____3117 = resugar_pat pat in
            let uu____3118 = resugar_term e in (uu____3117, uu____3118) in
          [uu____3112] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3136,t1)::(pat2,uu____3139,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3235 =
          let uu____3236 =
            let uu____3243 = resugar_term e in
            let uu____3244 = resugar_term t1 in
            let uu____3245 = resugar_term t2 in
            (uu____3243, uu____3244, uu____3245) in
          FStar_Parser_AST.If uu____3236 in
        mk1 uu____3235
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3303 =
          match uu____3303 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3334 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3334 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3338 =
          let uu____3339 =
            let uu____3354 = resugar_term e in
            let uu____3355 = FStar_List.map resugar_branch branches in
            (uu____3354, uu____3355) in
          FStar_Parser_AST.Match uu____3339 in
        mk1 uu____3338
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3395) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3462 =
          let uu____3463 =
            let uu____3472 = resugar_term e in (uu____3472, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3463 in
        mk1 uu____3462
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3496 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3496 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3521 =
                 let uu____3526 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3526 in
               match uu____3521 with
               | (univs1,td) ->
                   let uu____3537 =
                     let uu____3546 =
                       let uu____3547 = FStar_Syntax_Subst.compress td in
                       uu____3547.FStar_Syntax_Syntax.n in
                     match uu____3546 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3558,(t1,uu____3560)::(d,uu____3562)::[]) ->
                         (t1, d)
                     | uu____3605 -> failwith "wrong let binding format" in
                   (match uu____3537 with
                    | (typ,def) ->
                        let uu____3632 =
                          let uu____3639 =
                            let uu____3640 = FStar_Syntax_Subst.compress def in
                            uu____3640.FStar_Syntax_Syntax.n in
                          match uu____3639 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3651) ->
                              let uu____3672 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3672 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3686 =
                                       FStar_Options.print_implicits () in
                                     if uu____3686 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3688 -> ([], def, false) in
                        (match uu____3632 with
                         | (binders,term,is_pat_app) ->
                             let uu____3712 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3723 =
                                     let uu____3724 =
                                       let uu____3725 =
                                         let uu____3732 =
                                           bv_as_unique_ident bv in
                                         (uu____3732,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3725 in
                                     mk_pat uu____3724 in
                                   (uu____3723, term) in
                             (match uu____3712 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3768  ->
                                              match uu____3768 with
                                              | (bv,q) ->
                                                  let uu____3783 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3783
                                                    (fun q1  ->
                                                       let uu____3795 =
                                                         let uu____3796 =
                                                           let uu____3803 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3803, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3796 in
                                                       mk_pat uu____3795))) in
                                    let uu____3806 =
                                      let uu____3811 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3811) in
                                    let uu____3814 =
                                      universe_to_string univs1 in
                                    (uu____3806, uu____3814)
                                  else
                                    (let uu____3820 =
                                       let uu____3825 = resugar_term term1 in
                                       (pat, uu____3825) in
                                     let uu____3826 =
                                       universe_to_string univs1 in
                                     (uu____3820, uu____3826))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3872 =
                   let uu____3873 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3873 in
                 if uu____3872
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___240_3893  ->
                      match uu___240_3893 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3934) ->
        let s =
          let uu____3960 =
            let uu____3961 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3961 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____3960 in
        let uu____3962 = mk1 FStar_Parser_AST.Wild in label s uu____3962
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___241_3972 =
          match uu___241_3972 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____3993 =
                  let uu____3994 = FStar_Syntax_Subst.compress h in
                  uu____3994.FStar_Syntax_Syntax.n in
                match uu____3993 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4014 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4014, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4037 = head_fv_universes_args h1 in
                    (match uu____4037 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4125 = head_fv_universes_args head1 in
                    (match uu____4125 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4197 ->
                    let uu____4198 =
                      let uu____4199 =
                        let uu____4200 =
                          let uu____4201 = resugar_term h in
                          parser_term_to_string uu____4201 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4200 in
                      FStar_Errors.Err uu____4199 in
                    FStar_Exn.raise uu____4198 in
              let uu____4218 =
                try
                  let uu____4270 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4270
                with
                | FStar_Errors.Err uu____4291 ->
                    let uu____4292 =
                      let uu____4293 =
                        let uu____4298 =
                          let uu____4299 =
                            let uu____4300 = resugar_term e in
                            parser_term_to_string uu____4300 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4299 in
                        (uu____4298, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4293 in
                    FStar_Exn.raise uu____4292 in
              (match uu____4218 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4354 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4354, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4378  ->
                          match uu____4378 with
                          | (t1,q) ->
                              let uu____4397 = resugar_imp q in
                              (match uu____4397 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4407 =
                                     let uu____4412 = resugar_term t1 in
                                     (uu____4412, rimp) in
                                   FStar_Pervasives_Native.Some uu____4407
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4428 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4430 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4430) in
                     if uu____4428
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4453,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4478 =
                      let uu____4479 =
                        let uu____4488 = resugar_seq t11 in
                        (uu____4488, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4479 in
                    mk1 uu____4478
                | uu____4491 -> t1 in
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
               | uu____4513 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4515 =
                let uu____4516 = FStar_Syntax_Subst.compress e in
                uu____4516.FStar_Syntax_Syntax.n in
              (match uu____4515 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4520;
                      FStar_Syntax_Syntax.vars = uu____4521;_},(term,uu____4523)::[])
                   -> resugar_term term
               | uu____4552 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4590  ->
                       match uu____4590 with
                       | (x,uu____4596) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4598,p) ->
             let uu____4600 =
               let uu____4601 =
                 let uu____4608 = resugar_term e in (uu____4608, l, p) in
               FStar_Parser_AST.Labeled uu____4601 in
             mk1 uu____4600
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4610,s,uu____4612) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4617 ->
                  (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                     "Meta_alien was not a Tm_unknown";
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4626 =
               let uu____4627 =
                 let uu____4636 = resugar_term e in
                 let uu____4637 =
                   let uu____4638 =
                     let uu____4639 =
                       let uu____4650 =
                         let uu____4657 =
                           let uu____4662 = resugar_term t1 in
                           (uu____4662, FStar_Parser_AST.Nothing) in
                         [uu____4657] in
                       (name1, uu____4650) in
                     FStar_Parser_AST.Construct uu____4639 in
                   mk1 uu____4638 in
                 (uu____4636, uu____4637, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4627 in
             mk1 uu____4626
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4680,t1) ->
             let uu____4686 =
               let uu____4687 =
                 let uu____4696 = resugar_term e in
                 let uu____4697 =
                   let uu____4698 =
                     let uu____4699 =
                       let uu____4710 =
                         let uu____4717 =
                           let uu____4722 = resugar_term t1 in
                           (uu____4722, FStar_Parser_AST.Nothing) in
                         [uu____4717] in
                       (name1, uu____4710) in
                     FStar_Parser_AST.Construct uu____4699 in
                   mk1 uu____4698 in
                 (uu____4696, uu____4697, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4687 in
             mk1 uu____4686)
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
             let uu____4770 = FStar_Options.print_universes () in
             if uu____4770
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
             let uu____4831 = FStar_Options.print_universes () in
             if uu____4831
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
          let uu____4872 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4872, FStar_Parser_AST.Nothing) in
        let uu____4873 = FStar_Options.print_effect_args () in
        if uu____4873
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
                    let uu____4960 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____4960, (FStar_Pervasives_Native.snd post)) in
                  let uu____4969 =
                    let uu____4978 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____4978 then [] else [pre] in
                  let uu____5008 =
                    let uu____5017 =
                      let uu____5026 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5026 then [] else [pats] in
                    FStar_List.append [post1] uu____5017 in
                  FStar_List.append uu____4969 uu____5008
              | uu____5080 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5109  ->
                 match uu____5109 with
                 | (e,uu____5119) ->
                     let uu____5120 = resugar_term e in
                     (uu____5120, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___242_5141 =
            match uu___242_5141 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5174 = resugar_term e in
                       (uu____5174, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5179 -> aux l tl1) in
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
      let uu____5224 = b in
      match uu____5224 with
      | (x,aq) ->
          let uu____5229 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5229
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5243 =
                     let uu____5244 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5244 in
                   FStar_Parser_AST.mk_binder uu____5243 r
                     FStar_Parser_AST.Type_level imp
               | uu____5245 ->
                   let uu____5246 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5246
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5248 =
                        let uu____5249 =
                          let uu____5254 = bv_as_unique_ident x in
                          (uu____5254, e) in
                        FStar_Parser_AST.Annotated uu____5249 in
                      FStar_Parser_AST.mk_binder uu____5248 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5263 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5263 in
      let uu____5264 =
        let uu____5265 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5265.FStar_Syntax_Syntax.n in
      match uu____5264 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5273 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5273
          else
            (let uu____5275 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5275
               (fun aq  ->
                  let uu____5287 =
                    let uu____5288 =
                      let uu____5289 =
                        let uu____5296 = bv_as_unique_ident x in
                        (uu____5296, aq) in
                      FStar_Parser_AST.PatVar uu____5289 in
                    mk1 uu____5288 in
                  FStar_Pervasives_Native.Some uu____5287))
      | uu____5299 ->
          let uu____5300 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5300
            (fun aq  ->
               let pat =
                 let uu____5315 =
                   let uu____5316 =
                     let uu____5323 = bv_as_unique_ident x in
                     (uu____5323, aq) in
                   FStar_Parser_AST.PatVar uu____5316 in
                 mk1 uu____5315 in
               let uu____5326 = FStar_Options.print_bound_var_types () in
               if uu____5326
               then
                 let uu____5329 =
                   let uu____5330 =
                     let uu____5331 =
                       let uu____5336 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5336) in
                     FStar_Parser_AST.PatAscribed uu____5331 in
                   mk1 uu____5330 in
                 FStar_Pervasives_Native.Some uu____5329
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
              (fun uu____5413  ->
                 match uu____5413 with
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
              (fun uu____5448  ->
                 match uu____5448 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5455 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5455
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5461;
             FStar_Syntax_Syntax.fv_delta = uu____5462;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5489 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5489 FStar_List.rev in
          let args1 =
            let uu____5505 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5525  ->
                      match uu____5525 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5505 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5595 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5595
            | (hd1::tl1,hd2::tl2) ->
                let uu____5618 = map21 tl1 tl2 in (hd1, hd2) :: uu____5618 in
          let args2 =
            let uu____5636 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5636 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5687  ->
                 match uu____5687 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5697 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5697 with
           | FStar_Pervasives_Native.Some (op,uu____5705) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5714 =
                 let uu____5715 =
                   let uu____5722 = bv_as_unique_ident v1 in
                   let uu____5723 = to_arg_qual imp_opt in
                   (uu____5722, uu____5723) in
                 FStar_Parser_AST.PatVar uu____5715 in
               mk1 uu____5714)
      | FStar_Syntax_Syntax.Pat_wild uu____5728 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5736 =
              let uu____5737 =
                let uu____5744 = bv_as_unique_ident bv in
                (uu____5744,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5737 in
            mk1 uu____5736 in
          let uu____5747 = FStar_Options.print_bound_var_types () in
          if uu____5747
          then
            let uu____5748 =
              let uu____5749 =
                let uu____5754 = resugar_term term in (pat, uu____5754) in
              FStar_Parser_AST.PatAscribed uu____5749 in
            mk1 uu____5748
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___243_5760  ->
    match uu___243_5760 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5769 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5770 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5771 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5776 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5785 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5794 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___244_5797  ->
    match uu___244_5797 with
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
          (tylid,uvs,bs,t,uu____5824,datacons) ->
          let uu____5834 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5861,uu____5862,uu____5863,inductive_lid,uu____5865,uu____5866)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5871 -> failwith "unexpected")) in
          (match uu____5834 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5890 = FStar_Options.print_implicits () in
                 if uu____5890 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5900 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___245_5905  ->
                           match uu___245_5905 with
                           | FStar_Syntax_Syntax.RecordType uu____5906 ->
                               true
                           | uu____5915 -> false)) in
                 if uu____5900
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5963,univs1,term,uu____5966,num,uu____5968)
                         ->
                         let uu____5973 =
                           let uu____5974 = FStar_Syntax_Subst.compress term in
                           uu____5974.FStar_Syntax_Syntax.n in
                         (match uu____5973 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5988) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6049  ->
                                        match uu____6049 with
                                        | (b,qual) ->
                                            let uu____6064 =
                                              let uu____6065 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6065 in
                                            let uu____6066 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6064, uu____6066,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6077 -> failwith "unexpected")
                     | uu____6088 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6209,num,uu____6211) ->
                          let c =
                            let uu____6229 =
                              let uu____6232 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6232 in
                            ((l.FStar_Ident.ident), uu____6229,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6249 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6325 ->
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
        let uu____6343 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6343;
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
      let uu____6356 = ts in
      match uu____6356 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6364 =
            let uu____6365 =
              let uu____6378 =
                let uu____6387 =
                  let uu____6394 =
                    let uu____6395 =
                      let uu____6408 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6408) in
                    FStar_Parser_AST.TyconAbbrev uu____6395 in
                  (uu____6394, FStar_Pervasives_Native.None) in
                [uu____6387] in
              (false, uu____6378) in
            FStar_Parser_AST.Tycon uu____6365 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6364
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
            let uu____6462 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6462 with
            | (bs,action_defn) ->
                let uu____6469 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6469 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6477 = FStar_Options.print_implicits () in
                       if uu____6477
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6482 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6482 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6496 =
                           let uu____6507 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6507,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6496 in
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
          let uu____6581 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6581 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6589 = FStar_Options.print_implicits () in
                if uu____6589 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6594 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6594 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6651) ->
        let uu____6660 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6682 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6699 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6706 -> false
                  | uu____6721 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6660 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6753 se1 =
               match uu____6753 with
               | (datacon_ses1,tycons) ->
                   let uu____6779 = resugar_typ datacon_ses1 se1 in
                   (match uu____6779 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6794 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6794 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6829 =
                         let uu____6830 =
                           let uu____6831 =
                             let uu____6844 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6844) in
                           FStar_Parser_AST.Tycon uu____6831 in
                         decl'_to_decl se uu____6830 in
                       FStar_Pervasives_Native.Some uu____6829
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6875,uu____6876,uu____6877,uu____6878,uu____6879)
                            ->
                            let uu____6884 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6884
                        | uu____6887 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6890 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6896) ->
        let uu____6901 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___246_6907  ->
                  match uu___246_6907 with
                  | FStar_Syntax_Syntax.Projector (uu____6908,uu____6909) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6910 -> true
                  | uu____6911 -> false)) in
        if uu____6901
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6934) ->
               let uu____6947 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6947
           | uu____6954 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6958,fml) ->
        let uu____6960 =
          let uu____6961 =
            let uu____6962 =
              let uu____6967 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6967) in
            FStar_Parser_AST.Assume uu____6962 in
          decl'_to_decl se uu____6961 in
        FStar_Pervasives_Native.Some uu____6960
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6969 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6969
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6971 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6971
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6980,t) ->
              let uu____6992 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6992
          | uu____6993 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7001,t) ->
              let uu____7013 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7013
          | uu____7014 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7038 -> failwith "Should not happen hopefully" in
        let uu____7047 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7047
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7057 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7057 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7067 = FStar_Options.print_implicits () in
               if uu____7067 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7076 =
               let uu____7077 =
                 let uu____7078 =
                   let uu____7091 =
                     let uu____7100 =
                       let uu____7107 =
                         let uu____7108 =
                           let uu____7121 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7121) in
                         FStar_Parser_AST.TyconAbbrev uu____7108 in
                       (uu____7107, FStar_Pervasives_Native.None) in
                     [uu____7100] in
                   (false, uu____7091) in
                 FStar_Parser_AST.Tycon uu____7078 in
               decl'_to_decl se uu____7077 in
             FStar_Pervasives_Native.Some uu____7076)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7149 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7149
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7153 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___247_7159  ->
                  match uu___247_7159 with
                  | FStar_Syntax_Syntax.Projector (uu____7160,uu____7161) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7162 -> true
                  | uu____7163 -> false)) in
        if uu____7153
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7168 =
               (let uu____7171 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7171) || (FStar_List.isEmpty uvs) in
             if uu____7168
             then resugar_term t
             else
               (let uu____7173 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7173 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7181 = resugar_term t1 in
                    label universes uu____7181) in
           let uu____7182 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7182)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7183 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7200 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7215 -> FStar_Pervasives_Native.None