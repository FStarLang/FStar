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
         (fun uu___65_91  ->
            match uu___65_91 with
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
          let id1 =
            let uu____313 =
              let uu____318 =
                let uu____319 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____319 in
              (uu____318, r) in
            FStar_Ident.mk_ident uu____313 in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___66_338 =
      match uu___66_338 with
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
                    let uu____1009 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1009 in
                  let uu____1011 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1007 <> uu____1011) in
             if uu____1004
             then
               let uu____1014 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1014
             else
               (let uu____1016 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1016))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1023 = FStar_Options.print_universes () in
        if uu____1023
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1030 =
                   let uu____1031 =
                     let uu____1038 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1038, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1031 in
                 mk1 uu____1030) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1041 = FStar_Syntax_Syntax.is_teff t in
        if uu____1041
        then
          let uu____1042 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1042
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1045 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1045
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1046 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1046
         | uu____1047 ->
             let uu____1048 = FStar_Options.print_universes () in
             if uu____1048
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1066 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1066))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1069) ->
        let uu____1090 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1090 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1098 = FStar_Options.print_implicits () in
               if uu____1098 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1112  ->
                       match uu____1112 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1142 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1142 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1150 = FStar_Options.print_implicits () in
               if uu____1150 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1156 =
                 FStar_All.pipe_right xs2
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1156 FStar_List.rev in
             let rec aux body3 uu___67_1175 =
               match uu___67_1175 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1191 =
          let uu____1196 =
            let uu____1197 = FStar_Syntax_Syntax.mk_binder x in [uu____1197] in
          FStar_Syntax_Subst.open_term uu____1196 phi in
        (match uu____1191 with
         | (x1,phi1) ->
             let b =
               let uu____1201 =
                 let uu____1204 = FStar_List.hd x1 in
                 resugar_binder uu____1204 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1201 in
             let uu____1209 =
               let uu____1210 =
                 let uu____1215 = resugar_term phi1 in (b, uu____1215) in
               FStar_Parser_AST.Refine uu____1210 in
             mk1 uu____1209)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___68_1257 =
          match uu___68_1257 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1327 -> failwith "last of an empty list" in
        let rec last_two uu___69_1363 =
          match uu___69_1363 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1394::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1471::t1 -> last_two t1 in
        let rec last_three uu___70_1512 =
          match uu___70_1512 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1543::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1570::uu____1571::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1679::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1765  ->
                    match uu____1765 with
                    | (e2,qual) ->
                        let uu____1784 = resugar_term e2 in
                        (uu____1784, qual))) in
          let e2 = resugar_term e1 in
          let res_impl desugared_tm qual =
            let uu____1799 = resugar_imp qual in
            match uu____1799 with
            | FStar_Pervasives_Native.Some imp -> imp
            | FStar_Pervasives_Native.None  ->
                ((let uu____1804 =
                    let uu____1809 =
                      let uu____1810 = parser_term_to_string desugared_tm in
                      FStar_Util.format1
                        "Inaccessible argument %s in function application"
                        uu____1810 in
                    (FStar_Errors.Warning_InaccessibleArgument, uu____1809) in
                  FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1804);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1823  ->
                 match uu____1823 with
                 | (x,qual) ->
                     let uu____1836 =
                       let uu____1837 =
                         let uu____1844 = res_impl x qual in
                         (acc, x, uu____1844) in
                       FStar_Parser_AST.App uu____1837 in
                     mk1 uu____1836) e2 args2 in
        let args1 =
          let uu____1854 = FStar_Options.print_implicits () in
          if uu____1854 then args else filter_imp args in
        let uu____1866 = resugar_term_as_op e in
        (match uu____1866 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1877) ->
             (match args1 with
              | (fst1,uu____1883)::(snd1,uu____1885)::rest ->
                  let e1 =
                    let uu____1916 =
                      let uu____1917 =
                        let uu____1924 =
                          let uu____1927 = resugar_term fst1 in
                          let uu____1928 =
                            let uu____1931 = resugar_term snd1 in
                            [uu____1931] in
                          uu____1927 :: uu____1928 in
                        ((FStar_Ident.id_of_text "*"), uu____1924) in
                      FStar_Parser_AST.Op uu____1917 in
                    mk1 uu____1916 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1944  ->
                         match uu____1944 with
                         | (x,uu____1950) ->
                             let uu____1951 =
                               let uu____1952 =
                                 let uu____1959 =
                                   let uu____1962 =
                                     let uu____1965 = resugar_term x in
                                     [uu____1965] in
                                   e1 :: uu____1962 in
                                 ((FStar_Ident.id_of_text "*"), uu____1959) in
                               FStar_Parser_AST.Op uu____1952 in
                             mk1 uu____1951) e1 rest
              | uu____1968 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1977) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2003)::[] -> b
               | uu____2020 -> failwith "wrong arguments to dtuple" in
             let uu____2031 =
               let uu____2032 = FStar_Syntax_Subst.compress body in
               uu____2032.FStar_Syntax_Syntax.n in
             (match uu____2031 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2037) ->
                  let uu____2058 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2058 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2066 = FStar_Options.print_implicits () in
                         if uu____2066 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2078 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2099  ->
                            match uu____2099 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2111) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2117) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2122 = FStar_List.hd args1 in
             (match uu____2122 with
              | (t1,uu____2136) ->
                  let uu____2141 =
                    let uu____2142 = FStar_Syntax_Subst.compress t1 in
                    uu____2142.FStar_Syntax_Syntax.n in
                  (match uu____2141 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2147 =
                         let uu____2148 =
                           let uu____2153 = resugar_term t1 in
                           (uu____2153, f) in
                         FStar_Parser_AST.Project uu____2148 in
                       mk1 uu____2147
                   | uu____2154 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2155) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2175 =
               match new_args with
               | (a1,uu____2193)::(a2,uu____2195)::[] -> (a1, a2)
               | uu____2226 -> failwith "wrong arguments to try_with" in
             (match uu____2175 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2257 =
                      let uu____2258 = FStar_Syntax_Subst.compress term in
                      uu____2258.FStar_Syntax_Syntax.n in
                    match uu____2257 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2263) ->
                        let uu____2284 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2284 with | (x1,e2) -> e2)
                    | uu____2291 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2293 = decomp body in resugar_term uu____2293 in
                  let handler1 =
                    let uu____2295 = decomp handler in
                    resugar_term uu____2295 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2301,uu____2302,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2334,uu____2335,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2356 =
                          let uu____2357 =
                            let uu____2366 = resugar_body t11 in
                            (uu____2366, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2357 in
                        mk1 uu____2356
                    | uu____2369 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2424 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2454) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2460) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2545 -> (xs, pat, t1) in
             let resugar body =
               let uu____2556 =
                 let uu____2557 = FStar_Syntax_Subst.compress body in
                 uu____2557.FStar_Syntax_Syntax.n in
               match uu____2556 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2562) ->
                   let uu____2583 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2583 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2591 = FStar_Options.print_implicits () in
                          if uu____2591 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2600 =
                          let uu____2609 =
                            let uu____2610 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2610.FStar_Syntax_Syntax.n in
                          match uu____2609 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2679  ->
                                                 match uu____2679 with
                                                 | (e2,uu____2685) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2688) -> []
                                | uu____2691 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2700 ->
                              let uu____2701 = resugar_term body2 in
                              ([], uu____2701) in
                        (match uu____2600 with
                         | (pats,body3) ->
                             let uu____2718 = uncurry xs3 pats body3 in
                             (match uu____2718 with
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
               | uu____2766 ->
                   if op = "forall"
                   then
                     let uu____2767 =
                       let uu____2768 =
                         let uu____2781 = resugar_term body in
                         ([], [[]], uu____2781) in
                       FStar_Parser_AST.QForall uu____2768 in
                     mk1 uu____2767
                   else
                     (let uu____2793 =
                        let uu____2794 =
                          let uu____2807 = resugar_term body in
                          ([], [[]], uu____2807) in
                        FStar_Parser_AST.QExists uu____2794 in
                      mk1 uu____2793) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2834)::[] -> resugar b
                | uu____2851 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2861) ->
             let uu____2866 = FStar_List.hd args1 in
             (match uu____2866 with | (e1,uu____2880) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2925  ->
                       match uu____2925 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____2932 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2932 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2939 =
                         let uu____2940 =
                           let uu____2947 =
                             let uu____2950 = last1 args1 in
                             resugar uu____2950 in
                           (op1, uu____2947) in
                         FStar_Parser_AST.Op uu____2940 in
                       mk1 uu____2939
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2965 =
                         let uu____2966 =
                           let uu____2973 =
                             let uu____2976 = last_two args1 in
                             resugar uu____2976 in
                           (op1, uu____2973) in
                         FStar_Parser_AST.Op uu____2966 in
                       mk1 uu____2965
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2991 =
                         let uu____2992 =
                           let uu____2999 =
                             let uu____3002 = last_three args1 in
                             resugar uu____3002 in
                           (op1, uu____2999) in
                         FStar_Parser_AST.Op uu____2992 in
                       mk1 uu____2991
                   | uu____3011 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3018 =
                    let uu____3019 =
                      let uu____3026 =
                        let uu____3029 = last_two args1 in resugar uu____3029 in
                      (op1, uu____3026) in
                    FStar_Parser_AST.Op uu____3019 in
                  mk1 uu____3018
              | uu____3038 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3041,t1)::[]) ->
        let bnds =
          let uu____3114 =
            let uu____3119 = resugar_pat pat in
            let uu____3120 = resugar_term e in (uu____3119, uu____3120) in
          [uu____3114] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3138,t1)::(pat2,uu____3141,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3237 =
          let uu____3238 =
            let uu____3245 = resugar_term e in
            let uu____3246 = resugar_term t1 in
            let uu____3247 = resugar_term t2 in
            (uu____3245, uu____3246, uu____3247) in
          FStar_Parser_AST.If uu____3238 in
        mk1 uu____3237
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3305 =
          match uu____3305 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3336 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3336 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3340 =
          let uu____3341 =
            let uu____3356 = resugar_term e in
            let uu____3357 = FStar_List.map resugar_branch branches in
            (uu____3356, uu____3357) in
          FStar_Parser_AST.Match uu____3341 in
        mk1 uu____3340
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3397) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3464 =
          let uu____3465 =
            let uu____3474 = resugar_term e in (uu____3474, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3465 in
        mk1 uu____3464
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3498 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3498 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3523 =
                 let uu____3528 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3528 in
               match uu____3523 with
               | (univs1,td) ->
                   let uu____3539 =
                     let uu____3548 =
                       let uu____3549 = FStar_Syntax_Subst.compress td in
                       uu____3549.FStar_Syntax_Syntax.n in
                     match uu____3548 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3560,(t1,uu____3562)::(d,uu____3564)::[]) ->
                         (t1, d)
                     | uu____3607 -> failwith "wrong let binding format" in
                   (match uu____3539 with
                    | (typ,def) ->
                        let uu____3634 =
                          let uu____3641 =
                            let uu____3642 = FStar_Syntax_Subst.compress def in
                            uu____3642.FStar_Syntax_Syntax.n in
                          match uu____3641 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3653) ->
                              let uu____3674 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3674 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3688 =
                                       FStar_Options.print_implicits () in
                                     if uu____3688 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3690 -> ([], def, false) in
                        (match uu____3634 with
                         | (binders,term,is_pat_app) ->
                             let uu____3714 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3725 =
                                     let uu____3726 =
                                       let uu____3727 =
                                         let uu____3734 =
                                           bv_as_unique_ident bv in
                                         (uu____3734,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3727 in
                                     mk_pat uu____3726 in
                                   (uu____3725, term) in
                             (match uu____3714 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3770  ->
                                              match uu____3770 with
                                              | (bv,q) ->
                                                  let uu____3785 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3785
                                                    (fun q1  ->
                                                       let uu____3797 =
                                                         let uu____3798 =
                                                           let uu____3805 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3805, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3798 in
                                                       mk_pat uu____3797))) in
                                    let uu____3808 =
                                      let uu____3813 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3813) in
                                    let uu____3816 =
                                      universe_to_string univs1 in
                                    (uu____3808, uu____3816)
                                  else
                                    (let uu____3822 =
                                       let uu____3827 = resugar_term term1 in
                                       (pat, uu____3827) in
                                     let uu____3828 =
                                       universe_to_string univs1 in
                                     (uu____3822, uu____3828))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3874 =
                   let uu____3875 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3875 in
                 if uu____3874
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___71_3895  ->
                      match uu___71_3895 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3936) ->
        let s =
          let uu____3962 =
            let uu____3963 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3963 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____3962 in
        let uu____3964 = mk1 FStar_Parser_AST.Wild in label s uu____3964
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___72_3974 =
          match uu___72_3974 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____3995 =
                  let uu____3996 = FStar_Syntax_Subst.compress h in
                  uu____3996.FStar_Syntax_Syntax.n in
                match uu____3995 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4016 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4016, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4039 = head_fv_universes_args h1 in
                    (match uu____4039 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4127 = head_fv_universes_args head1 in
                    (match uu____4127 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4199 ->
                    let uu____4200 =
                      let uu____4205 =
                        let uu____4206 =
                          let uu____4207 = resugar_term h in
                          parser_term_to_string uu____4207 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4206 in
                      (FStar_Errors.Fatal_NotApplicationOrFv, uu____4205) in
                    FStar_Errors.raise_error uu____4200
                      e.FStar_Syntax_Syntax.pos in
              let uu____4224 =
                try
                  let uu____4276 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4276
                with
                | FStar_Errors.Err uu____4297 ->
                    let uu____4302 =
                      let uu____4307 =
                        let uu____4308 =
                          let uu____4309 = resugar_term e in
                          parser_term_to_string uu____4309 in
                        FStar_Util.format1 "wrong Data_app head format %s"
                          uu____4308 in
                      (FStar_Errors.Fatal_WrongDataAppHeadFormat, uu____4307) in
                    FStar_Errors.raise_error uu____4302
                      e.FStar_Syntax_Syntax.pos in
              (match uu____4224 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4363 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4363, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4387  ->
                          match uu____4387 with
                          | (t1,q) ->
                              let uu____4406 = resugar_imp q in
                              (match uu____4406 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4416 =
                                     let uu____4421 = resugar_term t1 in
                                     (uu____4421, rimp) in
                                   FStar_Pervasives_Native.Some uu____4416
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4437 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4439 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4439) in
                     if uu____4437
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4462,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4487 =
                      let uu____4488 =
                        let uu____4497 = resugar_seq t11 in
                        (uu____4497, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4488 in
                    mk1 uu____4487
                | uu____4500 -> t1 in
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
               | uu____4522 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4524 =
                let uu____4525 = FStar_Syntax_Subst.compress e in
                uu____4525.FStar_Syntax_Syntax.n in
              (match uu____4524 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4529;
                      FStar_Syntax_Syntax.vars = uu____4530;_},(term,uu____4532)::[])
                   -> resugar_term term
               | uu____4561 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4599  ->
                       match uu____4599 with
                       | (x,uu____4605) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4607,p) ->
             let uu____4609 =
               let uu____4610 =
                 let uu____4617 = resugar_term e in (uu____4617, l, p) in
               FStar_Parser_AST.Labeled uu____4610 in
             mk1 uu____4609
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4619,s,uu____4621) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4626 ->
                  (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                     (FStar_Errors.Warning_MetaAlienNotATmUnknown,
                       "Meta_alien was not a Tm_unknown");
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4635 =
               let uu____4636 =
                 let uu____4645 = resugar_term e in
                 let uu____4646 =
                   let uu____4647 =
                     let uu____4648 =
                       let uu____4659 =
                         let uu____4666 =
                           let uu____4671 = resugar_term t1 in
                           (uu____4671, FStar_Parser_AST.Nothing) in
                         [uu____4666] in
                       (name1, uu____4659) in
                     FStar_Parser_AST.Construct uu____4648 in
                   mk1 uu____4647 in
                 (uu____4645, uu____4646, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4636 in
             mk1 uu____4635
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4689,t1) ->
             let uu____4695 =
               let uu____4696 =
                 let uu____4705 = resugar_term e in
                 let uu____4706 =
                   let uu____4707 =
                     let uu____4708 =
                       let uu____4719 =
                         let uu____4726 =
                           let uu____4731 = resugar_term t1 in
                           (uu____4731, FStar_Parser_AST.Nothing) in
                         [uu____4726] in
                       (name1, uu____4719) in
                     FStar_Parser_AST.Construct uu____4708 in
                   mk1 uu____4707 in
                 (uu____4705, uu____4706, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4696 in
             mk1 uu____4695)
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
             let uu____4779 = FStar_Options.print_universes () in
             if uu____4779
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
             let uu____4840 = FStar_Options.print_universes () in
             if uu____4840
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
          let uu____4881 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4881, FStar_Parser_AST.Nothing) in
        let uu____4882 = FStar_Options.print_effect_args () in
        if uu____4882
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
                    let uu____4969 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____4969, (FStar_Pervasives_Native.snd post)) in
                  let uu____4978 =
                    let uu____4987 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____4987 then [] else [pre] in
                  let uu____5017 =
                    let uu____5026 =
                      let uu____5035 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5035 then [] else [pats] in
                    FStar_List.append [post1] uu____5026 in
                  FStar_List.append uu____4978 uu____5017
              | uu____5089 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5118  ->
                 match uu____5118 with
                 | (e,uu____5128) ->
                     let uu____5129 = resugar_term e in
                     (uu____5129, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___73_5150 =
            match uu___73_5150 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5183 = resugar_term e in
                       (uu____5183, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5188 -> aux l tl1) in
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
      let uu____5233 = b in
      match uu____5233 with
      | (x,aq) ->
          let uu____5238 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5238
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5252 =
                     let uu____5253 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5253 in
                   FStar_Parser_AST.mk_binder uu____5252 r
                     FStar_Parser_AST.Type_level imp
               | uu____5254 ->
                   let uu____5255 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5255
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5257 =
                        let uu____5258 =
                          let uu____5263 = bv_as_unique_ident x in
                          (uu____5263, e) in
                        FStar_Parser_AST.Annotated uu____5258 in
                      FStar_Parser_AST.mk_binder uu____5257 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5272 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5272 in
      let uu____5273 =
        let uu____5274 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5274.FStar_Syntax_Syntax.n in
      match uu____5273 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5282 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5282
          else
            (let uu____5284 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5284
               (fun aq  ->
                  let uu____5296 =
                    let uu____5297 =
                      let uu____5298 =
                        let uu____5305 = bv_as_unique_ident x in
                        (uu____5305, aq) in
                      FStar_Parser_AST.PatVar uu____5298 in
                    mk1 uu____5297 in
                  FStar_Pervasives_Native.Some uu____5296))
      | uu____5308 ->
          let uu____5309 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5309
            (fun aq  ->
               let pat =
                 let uu____5324 =
                   let uu____5325 =
                     let uu____5332 = bv_as_unique_ident x in
                     (uu____5332, aq) in
                   FStar_Parser_AST.PatVar uu____5325 in
                 mk1 uu____5324 in
               let uu____5335 = FStar_Options.print_bound_var_types () in
               if uu____5335
               then
                 let uu____5338 =
                   let uu____5339 =
                     let uu____5340 =
                       let uu____5345 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5345) in
                     FStar_Parser_AST.PatAscribed uu____5340 in
                   mk1 uu____5339 in
                 FStar_Pervasives_Native.Some uu____5338
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
              (fun uu____5422  ->
                 match uu____5422 with
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
              (fun uu____5457  ->
                 match uu____5457 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5464 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5464
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5470;
             FStar_Syntax_Syntax.fv_delta = uu____5471;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5498 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5498 FStar_List.rev in
          let args1 =
            let uu____5514 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5534  ->
                      match uu____5534 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5514 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5604 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5604
            | (hd1::tl1,hd2::tl2) ->
                let uu____5627 = map21 tl1 tl2 in (hd1, hd2) :: uu____5627 in
          let args2 =
            let uu____5645 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5645 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5696  ->
                 match uu____5696 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5706 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5706 with
           | FStar_Pervasives_Native.Some (op,uu____5714) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5723 =
                 let uu____5724 =
                   let uu____5731 = bv_as_unique_ident v1 in
                   let uu____5732 = to_arg_qual imp_opt in
                   (uu____5731, uu____5732) in
                 FStar_Parser_AST.PatVar uu____5724 in
               mk1 uu____5723)
      | FStar_Syntax_Syntax.Pat_wild uu____5737 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5745 =
              let uu____5746 =
                let uu____5753 = bv_as_unique_ident bv in
                (uu____5753,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5746 in
            mk1 uu____5745 in
          let uu____5756 = FStar_Options.print_bound_var_types () in
          if uu____5756
          then
            let uu____5757 =
              let uu____5758 =
                let uu____5763 = resugar_term term in (pat, uu____5763) in
              FStar_Parser_AST.PatAscribed uu____5758 in
            mk1 uu____5757
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___74_5769  ->
    match uu___74_5769 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5778 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5779 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5780 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5785 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5794 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5803 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___75_5806  ->
    match uu___75_5806 with
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
          (tylid,uvs,bs,t,uu____5833,datacons) ->
          let uu____5843 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5870,uu____5871,uu____5872,inductive_lid,uu____5874,uu____5875)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5880 -> failwith "unexpected")) in
          (match uu____5843 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5899 = FStar_Options.print_implicits () in
                 if uu____5899 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5909 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___76_5914  ->
                           match uu___76_5914 with
                           | FStar_Syntax_Syntax.RecordType uu____5915 ->
                               true
                           | uu____5924 -> false)) in
                 if uu____5909
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5972,univs1,term,uu____5975,num,uu____5977)
                         ->
                         let uu____5982 =
                           let uu____5983 = FStar_Syntax_Subst.compress term in
                           uu____5983.FStar_Syntax_Syntax.n in
                         (match uu____5982 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5997) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6058  ->
                                        match uu____6058 with
                                        | (b,qual) ->
                                            let uu____6073 =
                                              let uu____6074 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6074 in
                                            let uu____6075 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6073, uu____6075,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6086 -> failwith "unexpected")
                     | uu____6097 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6218,num,uu____6220) ->
                          let c =
                            let uu____6238 =
                              let uu____6241 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6241 in
                            ((l.FStar_Ident.ident), uu____6238,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6258 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6334 ->
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
        let uu____6352 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6352;
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
      let uu____6365 = ts in
      match uu____6365 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6373 =
            let uu____6374 =
              let uu____6387 =
                let uu____6396 =
                  let uu____6403 =
                    let uu____6404 =
                      let uu____6417 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6417) in
                    FStar_Parser_AST.TyconAbbrev uu____6404 in
                  (uu____6403, FStar_Pervasives_Native.None) in
                [uu____6396] in
              (false, uu____6387) in
            FStar_Parser_AST.Tycon uu____6374 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6373
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
            let uu____6471 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6471 with
            | (bs,action_defn) ->
                let uu____6478 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6478 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6486 = FStar_Options.print_implicits () in
                       if uu____6486
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6491 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6491 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6505 =
                           let uu____6516 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6516,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6505 in
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
          let uu____6590 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6590 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6598 = FStar_Options.print_implicits () in
                if uu____6598 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6603 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6603 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6660) ->
        let uu____6669 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6691 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6708 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6715 -> false
                  | uu____6730 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6669 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6762 se1 =
               match uu____6762 with
               | (datacon_ses1,tycons) ->
                   let uu____6788 = resugar_typ datacon_ses1 se1 in
                   (match uu____6788 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6803 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6803 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6838 =
                         let uu____6839 =
                           let uu____6840 =
                             let uu____6853 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6853) in
                           FStar_Parser_AST.Tycon uu____6840 in
                         decl'_to_decl se uu____6839 in
                       FStar_Pervasives_Native.Some uu____6838
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6884,uu____6885,uu____6886,uu____6887,uu____6888)
                            ->
                            let uu____6893 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6893
                        | uu____6896 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6899 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6905) ->
        let uu____6910 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___77_6916  ->
                  match uu___77_6916 with
                  | FStar_Syntax_Syntax.Projector (uu____6917,uu____6918) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6919 -> true
                  | uu____6920 -> false)) in
        if uu____6910
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6943) ->
               let uu____6956 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6956
           | uu____6963 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6967,fml) ->
        let uu____6969 =
          let uu____6970 =
            let uu____6971 =
              let uu____6976 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6976) in
            FStar_Parser_AST.Assume uu____6971 in
          decl'_to_decl se uu____6970 in
        FStar_Pervasives_Native.Some uu____6969
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6978 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6978
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6980 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6980
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6989,t) ->
              let uu____7001 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7001
          | uu____7002 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7010,t) ->
              let uu____7022 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7022
          | uu____7023 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7047 -> failwith "Should not happen hopefully" in
        let uu____7056 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7056
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
        let uu____7066 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7066 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7076 = FStar_Options.print_implicits () in
               if uu____7076 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7085 =
               let uu____7086 =
                 let uu____7087 =
                   let uu____7100 =
                     let uu____7109 =
                       let uu____7116 =
                         let uu____7117 =
                           let uu____7130 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7130) in
                         FStar_Parser_AST.TyconAbbrev uu____7117 in
                       (uu____7116, FStar_Pervasives_Native.None) in
                     [uu____7109] in
                   (false, uu____7100) in
                 FStar_Parser_AST.Tycon uu____7087 in
               decl'_to_decl se uu____7086 in
             FStar_Pervasives_Native.Some uu____7085)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7158 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7158
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7162 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___78_7168  ->
                  match uu___78_7168 with
                  | FStar_Syntax_Syntax.Projector (uu____7169,uu____7170) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7171 -> true
                  | uu____7172 -> false)) in
        if uu____7162
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7177 =
               (let uu____7180 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7180) || (FStar_List.isEmpty uvs) in
             if uu____7177
             then resugar_term t
             else
               (let uu____7182 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7182 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7190 = resugar_term t1 in
                    label universes uu____7190) in
           let uu____7191 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7191)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7192 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7209 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7224 -> FStar_Pervasives_Native.None