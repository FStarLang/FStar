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
         (fun uu___66_91  ->
            match uu___66_91 with
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
    let name_of_op uu___67_338 =
      match uu___67_338 with
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
             let rec aux body3 uu___68_1175 =
               match uu___68_1175 with
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
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.pos = uu____1217;
           FStar_Syntax_Syntax.vars = uu____1218;_},(e,uu____1220)::[])
        when
        (let uu____1251 = FStar_Options.print_implicits () in
         Prims.op_Negation uu____1251) &&
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
        -> resugar_term e
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___69_1293 =
          match uu___69_1293 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1363 -> failwith "last of an empty list" in
        let rec last_two uu___70_1399 =
          match uu___70_1399 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1430::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1507::t1 -> last_two t1 in
        let rec last_three uu___71_1548 =
          match uu___71_1548 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1579::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1606::uu____1607::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1715::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1801  ->
                    match uu____1801 with
                    | (e2,qual) ->
                        let uu____1820 = resugar_term e2 in
                        (uu____1820, qual))) in
          let e2 = resugar_term e1 in
          let res_impl desugared_tm qual =
            let uu____1835 = resugar_imp qual in
            match uu____1835 with
            | FStar_Pervasives_Native.Some imp -> imp
            | FStar_Pervasives_Native.None  ->
                ((let uu____1840 =
                    let uu____1845 =
                      let uu____1846 = parser_term_to_string desugared_tm in
                      FStar_Util.format1
                        "Inaccessible argument %s in function application"
                        uu____1846 in
                    (FStar_Errors.Warning_InaccessibleArgument, uu____1845) in
                  FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1840);
                 FStar_Parser_AST.Nothing) in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1859  ->
                 match uu____1859 with
                 | (x,qual) ->
                     let uu____1872 =
                       let uu____1873 =
                         let uu____1880 = res_impl x qual in
                         (acc, x, uu____1880) in
                       FStar_Parser_AST.App uu____1873 in
                     mk1 uu____1872) e2 args2 in
        let args1 =
          let uu____1890 = FStar_Options.print_implicits () in
          if uu____1890 then args else filter_imp args in
        let uu____1902 = resugar_term_as_op e in
        (match uu____1902 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1913) ->
             (match args1 with
              | (fst1,uu____1919)::(snd1,uu____1921)::rest ->
                  let e1 =
                    let uu____1952 =
                      let uu____1953 =
                        let uu____1960 =
                          let uu____1963 = resugar_term fst1 in
                          let uu____1964 =
                            let uu____1967 = resugar_term snd1 in
                            [uu____1967] in
                          uu____1963 :: uu____1964 in
                        ((FStar_Ident.id_of_text "*"), uu____1960) in
                      FStar_Parser_AST.Op uu____1953 in
                    mk1 uu____1952 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1980  ->
                         match uu____1980 with
                         | (x,uu____1986) ->
                             let uu____1987 =
                               let uu____1988 =
                                 let uu____1995 =
                                   let uu____1998 =
                                     let uu____2001 = resugar_term x in
                                     [uu____2001] in
                                   e1 :: uu____1998 in
                                 ((FStar_Ident.id_of_text "*"), uu____1995) in
                               FStar_Parser_AST.Op uu____1988 in
                             mk1 uu____1987) e1 rest
              | uu____2004 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2013) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2039)::[] -> b
               | uu____2056 -> failwith "wrong arguments to dtuple" in
             let uu____2067 =
               let uu____2068 = FStar_Syntax_Subst.compress body in
               uu____2068.FStar_Syntax_Syntax.n in
             (match uu____2067 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2073) ->
                  let uu____2094 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2094 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2102 = FStar_Options.print_implicits () in
                         if uu____2102 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           ((map_opt ())
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2114 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2135  ->
                            match uu____2135 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2147) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2153) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2158 = FStar_List.hd args1 in
             (match uu____2158 with
              | (t1,uu____2172) ->
                  let uu____2177 =
                    let uu____2178 = FStar_Syntax_Subst.compress t1 in
                    uu____2178.FStar_Syntax_Syntax.n in
                  (match uu____2177 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2183 =
                         let uu____2184 =
                           let uu____2189 = resugar_term t1 in
                           (uu____2189, f) in
                         FStar_Parser_AST.Project uu____2184 in
                       mk1 uu____2183
                   | uu____2190 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2191) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2211 =
               match new_args with
               | (a1,uu____2229)::(a2,uu____2231)::[] -> (a1, a2)
               | uu____2262 -> failwith "wrong arguments to try_with" in
             (match uu____2211 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2293 =
                      let uu____2294 = FStar_Syntax_Subst.compress term in
                      uu____2294.FStar_Syntax_Syntax.n in
                    match uu____2293 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2299) ->
                        let uu____2320 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2320 with | (x1,e2) -> e2)
                    | uu____2327 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2329 = decomp body in resugar_term uu____2329 in
                  let handler1 =
                    let uu____2331 = decomp handler in
                    resugar_term uu____2331 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2337,uu____2338,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2370,uu____2371,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2392 =
                          let uu____2393 =
                            let uu____2402 = resugar_body t11 in
                            (uu____2402, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2393 in
                        mk1 uu____2392
                    | uu____2405 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2460 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2490) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2496) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2581 -> (xs, pat, t1) in
             let resugar body =
               let uu____2592 =
                 let uu____2593 = FStar_Syntax_Subst.compress body in
                 uu____2593.FStar_Syntax_Syntax.n in
               match uu____2592 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2598) ->
                   let uu____2619 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2619 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2627 = FStar_Options.print_implicits () in
                          if uu____2627 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2636 =
                          let uu____2645 =
                            let uu____2646 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2646.FStar_Syntax_Syntax.n in
                          match uu____2645 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let uu____2664 =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    let uu____2692 =
                                      FStar_List.map
                                        (fun es  ->
                                           FStar_All.pipe_right es
                                             (FStar_List.map
                                                (fun uu____2728  ->
                                                   match uu____2728 with
                                                   | (e2,uu____2734) ->
                                                       resugar_term e2)))
                                        pats in
                                    (uu____2692, body3)
                                | FStar_Syntax_Syntax.Meta_labeled (s,r,p) ->
                                    let uu____2742 =
                                      mk1
                                        (FStar_Parser_AST.Labeled
                                           (body3, s, p)) in
                                    ([], uu____2742)
                                | uu____2749 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (match uu____2664 with
                               | (pats,body4) -> (pats, body4))
                          | uu____2780 ->
                              let uu____2781 = resugar_term body2 in
                              ([], uu____2781) in
                        (match uu____2636 with
                         | (pats,body3) ->
                             let uu____2798 = uncurry xs3 pats body3 in
                             (match uu____2798 with
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
               | uu____2846 ->
                   if op = "forall"
                   then
                     let uu____2847 =
                       let uu____2848 =
                         let uu____2861 = resugar_term body in
                         ([], [[]], uu____2861) in
                       FStar_Parser_AST.QForall uu____2848 in
                     mk1 uu____2847
                   else
                     (let uu____2873 =
                        let uu____2874 =
                          let uu____2887 = resugar_term body in
                          ([], [[]], uu____2887) in
                        FStar_Parser_AST.QExists uu____2874 in
                      mk1 uu____2873) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2914)::[] -> resugar b
                | uu____2931 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2941) ->
             let uu____2946 = FStar_List.hd args1 in
             (match uu____2946 with | (e1,uu____2960) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____3005  ->
                       match uu____3005 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____3012 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____3012 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____3019 =
                         let uu____3020 =
                           let uu____3027 =
                             let uu____3030 = last1 args1 in
                             resugar uu____3030 in
                           (op1, uu____3027) in
                         FStar_Parser_AST.Op uu____3020 in
                       mk1 uu____3019
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____3045 =
                         let uu____3046 =
                           let uu____3053 =
                             let uu____3056 = last_two args1 in
                             resugar uu____3056 in
                           (op1, uu____3053) in
                         FStar_Parser_AST.Op uu____3046 in
                       mk1 uu____3045
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3071 =
                         let uu____3072 =
                           let uu____3079 =
                             let uu____3082 = last_three args1 in
                             resugar uu____3082 in
                           (op1, uu____3079) in
                         FStar_Parser_AST.Op uu____3072 in
                       mk1 uu____3071
                   | uu____3091 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3098 =
                    let uu____3099 =
                      let uu____3106 =
                        let uu____3109 = last_two args1 in resugar uu____3109 in
                      (op1, uu____3106) in
                    FStar_Parser_AST.Op uu____3099 in
                  mk1 uu____3098
              | uu____3118 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3121,t1)::[]) ->
        let bnds =
          let uu____3194 =
            let uu____3199 = resugar_pat pat in
            let uu____3200 = resugar_term e in (uu____3199, uu____3200) in
          [uu____3194] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3218,t1)::(pat2,uu____3221,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3317 =
          let uu____3318 =
            let uu____3325 = resugar_term e in
            let uu____3326 = resugar_term t1 in
            let uu____3327 = resugar_term t2 in
            (uu____3325, uu____3326, uu____3327) in
          FStar_Parser_AST.If uu____3318 in
        mk1 uu____3317
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3385 =
          match uu____3385 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3416 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3416 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3420 =
          let uu____3421 =
            let uu____3436 = resugar_term e in
            let uu____3437 = FStar_List.map resugar_branch branches in
            (uu____3436, uu____3437) in
          FStar_Parser_AST.Match uu____3421 in
        mk1 uu____3420
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3477) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3544 =
          let uu____3545 =
            let uu____3554 = resugar_term e in (uu____3554, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3545 in
        mk1 uu____3544
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3578 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3578 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3603 =
                 let uu____3608 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3608 in
               match uu____3603 with
               | (univs1,td) ->
                   let uu____3619 =
                     let uu____3628 =
                       let uu____3629 = FStar_Syntax_Subst.compress td in
                       uu____3629.FStar_Syntax_Syntax.n in
                     match uu____3628 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3640,(t1,uu____3642)::(d,uu____3644)::[]) ->
                         (t1, d)
                     | uu____3687 -> failwith "wrong let binding format" in
                   (match uu____3619 with
                    | (typ,def) ->
                        let uu____3714 =
                          let uu____3721 =
                            let uu____3722 = FStar_Syntax_Subst.compress def in
                            uu____3722.FStar_Syntax_Syntax.n in
                          match uu____3721 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3733) ->
                              let uu____3754 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3754 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3768 =
                                       FStar_Options.print_implicits () in
                                     if uu____3768 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3770 -> ([], def, false) in
                        (match uu____3714 with
                         | (binders,term,is_pat_app) ->
                             let uu____3794 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3805 =
                                     let uu____3806 =
                                       let uu____3807 =
                                         let uu____3814 =
                                           bv_as_unique_ident bv in
                                         (uu____3814,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3807 in
                                     mk_pat uu____3806 in
                                   (uu____3805, term) in
                             (match uu____3794 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        ((map_opt ())
                                           (fun uu____3850  ->
                                              match uu____3850 with
                                              | (bv,q) ->
                                                  let uu____3865 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3865
                                                    (fun q1  ->
                                                       let uu____3877 =
                                                         let uu____3878 =
                                                           let uu____3885 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3885, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3878 in
                                                       mk_pat uu____3877))) in
                                    let uu____3888 =
                                      let uu____3893 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3893) in
                                    let uu____3896 =
                                      universe_to_string univs1 in
                                    (uu____3888, uu____3896)
                                  else
                                    (let uu____3902 =
                                       let uu____3907 = resugar_term term1 in
                                       (pat, uu____3907) in
                                     let uu____3908 =
                                       universe_to_string univs1 in
                                     (uu____3902, uu____3908))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3954 =
                   let uu____3955 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3955 in
                 if uu____3954
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___72_3975  ->
                      match uu___72_3975 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____4016) ->
        let s =
          let uu____4042 =
            let uu____4043 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____4043 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____4042 in
        let uu____4044 = mk1 FStar_Parser_AST.Wild in label s uu____4044
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___73_4054 =
          match uu___73_4054 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4075 =
                  let uu____4076 = FStar_Syntax_Subst.compress h in
                  uu____4076.FStar_Syntax_Syntax.n in
                match uu____4075 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4096 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4096, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4119 = head_fv_universes_args h1 in
                    (match uu____4119 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4207 = head_fv_universes_args head1 in
                    (match uu____4207 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4279 ->
                    let uu____4280 =
                      let uu____4285 =
                        let uu____4286 =
                          let uu____4287 = resugar_term h in
                          parser_term_to_string uu____4287 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4286 in
                      (FStar_Errors.Fatal_NotApplicationOrFv, uu____4285) in
                    FStar_Errors.raise_error uu____4280
                      e.FStar_Syntax_Syntax.pos in
              let uu____4304 =
                try
                  let uu____4356 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4356
                with
                | FStar_Errors.Err uu____4377 ->
                    let uu____4382 =
                      let uu____4387 =
                        let uu____4388 =
                          let uu____4389 = resugar_term e in
                          parser_term_to_string uu____4389 in
                        FStar_Util.format1 "wrong Data_app head format %s"
                          uu____4388 in
                      (FStar_Errors.Fatal_WrongDataAppHeadFormat, uu____4387) in
                    FStar_Errors.raise_error uu____4382
                      e.FStar_Syntax_Syntax.pos in
              (match uu____4304 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4443 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4443, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4467  ->
                          match uu____4467 with
                          | (t1,q) ->
                              let uu____4486 = resugar_imp q in
                              (match uu____4486 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4496 =
                                     let uu____4501 = resugar_term t1 in
                                     (uu____4501, rimp) in
                                   FStar_Pervasives_Native.Some uu____4496
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4517 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4519 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4519) in
                     if uu____4517
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4542,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4567 =
                      let uu____4568 =
                        let uu____4577 = resugar_seq t11 in
                        (uu____4577, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4568 in
                    mk1 uu____4567
                | uu____4580 -> t1 in
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
               | uu____4602 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4604 =
                let uu____4605 = FStar_Syntax_Subst.compress e in
                uu____4605.FStar_Syntax_Syntax.n in
              (match uu____4604 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4609;
                      FStar_Syntax_Syntax.vars = uu____4610;_},(term,uu____4612)::[])
                   -> resugar_term term
               | uu____4641 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4679  ->
                       match uu____4679 with
                       | (x,uu____4685) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4687,p) ->
             let uu____4689 =
               let uu____4690 =
                 let uu____4697 = resugar_term e in (uu____4697, l, p) in
               FStar_Parser_AST.Labeled uu____4690 in
             mk1 uu____4689
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4699,s,uu____4701) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____4706 ->
                  (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                     (FStar_Errors.Warning_MetaAlienNotATmUnknown,
                       "Meta_alien was not a Tm_unknown");
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4715 =
               let uu____4716 =
                 let uu____4725 = resugar_term e in
                 let uu____4726 =
                   let uu____4727 =
                     let uu____4728 =
                       let uu____4739 =
                         let uu____4746 =
                           let uu____4751 = resugar_term t1 in
                           (uu____4751, FStar_Parser_AST.Nothing) in
                         [uu____4746] in
                       (name1, uu____4739) in
                     FStar_Parser_AST.Construct uu____4728 in
                   mk1 uu____4727 in
                 (uu____4725, uu____4726, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4716 in
             mk1 uu____4715
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4769,t1) ->
             let uu____4775 =
               let uu____4776 =
                 let uu____4785 = resugar_term e in
                 let uu____4786 =
                   let uu____4787 =
                     let uu____4788 =
                       let uu____4799 =
                         let uu____4806 =
                           let uu____4811 = resugar_term t1 in
                           (uu____4811, FStar_Parser_AST.Nothing) in
                         [uu____4806] in
                       (name1, uu____4799) in
                     FStar_Parser_AST.Construct uu____4788 in
                   mk1 uu____4787 in
                 (uu____4785, uu____4786, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4776 in
             mk1 uu____4775)
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
             let uu____4859 = FStar_Options.print_universes () in
             if uu____4859
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
             let uu____4920 = FStar_Options.print_universes () in
             if uu____4920
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
          let uu____4961 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4961, FStar_Parser_AST.Nothing) in
        let uu____4962 = FStar_Options.print_effect_args () in
        if uu____4962
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
                    let uu____5049 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____5049, (FStar_Pervasives_Native.snd post)) in
                  let uu____5058 =
                    let uu____5067 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____5067 then [] else [pre] in
                  let uu____5097 =
                    let uu____5106 =
                      let uu____5115 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5115 then [] else [pats] in
                    FStar_List.append [post1] uu____5106 in
                  FStar_List.append uu____5058 uu____5097
              | uu____5169 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5198  ->
                 match uu____5198 with
                 | (e,uu____5208) ->
                     let uu____5209 = resugar_term e in
                     (uu____5209, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___74_5230 =
            match uu___74_5230 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5263 = resugar_term e in
                       (uu____5263, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5268 -> aux l tl1) in
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
      let uu____5313 = b in
      match uu____5313 with
      | (x,aq) ->
          let uu____5318 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5318
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5332 =
                     let uu____5333 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5333 in
                   FStar_Parser_AST.mk_binder uu____5332 r
                     FStar_Parser_AST.Type_level imp
               | uu____5334 ->
                   let uu____5335 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5335
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5337 =
                        let uu____5338 =
                          let uu____5343 = bv_as_unique_ident x in
                          (uu____5343, e) in
                        FStar_Parser_AST.Annotated uu____5338 in
                      FStar_Parser_AST.mk_binder uu____5337 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5352 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5352 in
      let uu____5353 =
        let uu____5354 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5354.FStar_Syntax_Syntax.n in
      match uu____5353 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5362 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5362
          else
            (let uu____5364 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5364
               (fun aq  ->
                  let uu____5376 =
                    let uu____5377 =
                      let uu____5378 =
                        let uu____5385 = bv_as_unique_ident x in
                        (uu____5385, aq) in
                      FStar_Parser_AST.PatVar uu____5378 in
                    mk1 uu____5377 in
                  FStar_Pervasives_Native.Some uu____5376))
      | uu____5388 ->
          let uu____5389 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5389
            (fun aq  ->
               let pat =
                 let uu____5404 =
                   let uu____5405 =
                     let uu____5412 = bv_as_unique_ident x in
                     (uu____5412, aq) in
                   FStar_Parser_AST.PatVar uu____5405 in
                 mk1 uu____5404 in
               let uu____5415 = FStar_Options.print_bound_var_types () in
               if uu____5415
               then
                 let uu____5418 =
                   let uu____5419 =
                     let uu____5420 =
                       let uu____5425 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5425) in
                     FStar_Parser_AST.PatAscribed uu____5420 in
                   mk1 uu____5419 in
                 FStar_Pervasives_Native.Some uu____5418
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
              (fun uu____5502  ->
                 match uu____5502 with
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
              (fun uu____5537  ->
                 match uu____5537 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5544 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5544
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5550;
             FStar_Syntax_Syntax.fv_delta = uu____5551;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5578 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5578 FStar_List.rev in
          let args1 =
            let uu____5594 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5614  ->
                      match uu____5614 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5594 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5684 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5684
            | (hd1::tl1,hd2::tl2) ->
                let uu____5707 = map21 tl1 tl2 in (hd1, hd2) :: uu____5707 in
          let args2 =
            let uu____5725 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5725 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5776  ->
                 match uu____5776 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5786 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5786 with
           | FStar_Pervasives_Native.Some (op,uu____5794) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5803 =
                 let uu____5804 =
                   let uu____5811 = bv_as_unique_ident v1 in
                   let uu____5812 = to_arg_qual imp_opt in
                   (uu____5811, uu____5812) in
                 FStar_Parser_AST.PatVar uu____5804 in
               mk1 uu____5803)
      | FStar_Syntax_Syntax.Pat_wild uu____5817 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5825 =
              let uu____5826 =
                let uu____5833 = bv_as_unique_ident bv in
                (uu____5833,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5826 in
            mk1 uu____5825 in
          let uu____5836 = FStar_Options.print_bound_var_types () in
          if uu____5836
          then
            let uu____5837 =
              let uu____5838 =
                let uu____5843 = resugar_term term in (pat, uu____5843) in
              FStar_Parser_AST.PatAscribed uu____5838 in
            mk1 uu____5837
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___75_5849  ->
    match uu___75_5849 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5858 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5859 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5860 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5865 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5874 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5883 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___76_5886  ->
    match uu___76_5886 with
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
          (tylid,uvs,bs,t,uu____5913,datacons) ->
          let uu____5923 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5950,uu____5951,uu____5952,inductive_lid,uu____5954,uu____5955)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5960 -> failwith "unexpected")) in
          (match uu____5923 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5979 = FStar_Options.print_implicits () in
                 if uu____5979 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5989 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___77_5994  ->
                           match uu___77_5994 with
                           | FStar_Syntax_Syntax.RecordType uu____5995 ->
                               true
                           | uu____6004 -> false)) in
                 if uu____5989
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____6052,univs1,term,uu____6055,num,uu____6057)
                         ->
                         let uu____6062 =
                           let uu____6063 = FStar_Syntax_Subst.compress term in
                           uu____6063.FStar_Syntax_Syntax.n in
                         (match uu____6062 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6077) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6138  ->
                                        match uu____6138 with
                                        | (b,qual) ->
                                            let uu____6153 =
                                              let uu____6154 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6154 in
                                            let uu____6155 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6153, uu____6155,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6166 -> failwith "unexpected")
                     | uu____6177 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6298,num,uu____6300) ->
                          let c =
                            let uu____6318 =
                              let uu____6321 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6321 in
                            ((l.FStar_Ident.ident), uu____6318,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6338 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6414 ->
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
        let uu____6432 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6432;
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
      let uu____6445 = ts in
      match uu____6445 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6453 =
            let uu____6454 =
              let uu____6467 =
                let uu____6476 =
                  let uu____6483 =
                    let uu____6484 =
                      let uu____6497 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6497) in
                    FStar_Parser_AST.TyconAbbrev uu____6484 in
                  (uu____6483, FStar_Pervasives_Native.None) in
                [uu____6476] in
              (false, uu____6467) in
            FStar_Parser_AST.Tycon uu____6454 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6453
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
            let uu____6551 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6551 with
            | (bs,action_defn) ->
                let uu____6558 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6558 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6566 = FStar_Options.print_implicits () in
                       if uu____6566
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6571 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6571 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6585 =
                           let uu____6596 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6596,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6585 in
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
          let uu____6670 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6670 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6678 = FStar_Options.print_implicits () in
                if uu____6678 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6683 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6683 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6740) ->
        let uu____6749 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6771 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6788 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6795 -> false
                  | uu____6810 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6749 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6842 se1 =
               match uu____6842 with
               | (datacon_ses1,tycons) ->
                   let uu____6868 = resugar_typ datacon_ses1 se1 in
                   (match uu____6868 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6883 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6883 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6918 =
                         let uu____6919 =
                           let uu____6920 =
                             let uu____6933 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6933) in
                           FStar_Parser_AST.Tycon uu____6920 in
                         decl'_to_decl se uu____6919 in
                       FStar_Pervasives_Native.Some uu____6918
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6964,uu____6965,uu____6966,uu____6967,uu____6968)
                            ->
                            let uu____6973 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6973
                        | uu____6976 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6979 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6985) ->
        let uu____6990 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___78_6996  ->
                  match uu___78_6996 with
                  | FStar_Syntax_Syntax.Projector (uu____6997,uu____6998) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6999 -> true
                  | uu____7000 -> false)) in
        if uu____6990
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____7023) ->
               let uu____7036 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____7036
           | uu____7043 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____7047,fml) ->
        let uu____7049 =
          let uu____7050 =
            let uu____7051 =
              let uu____7056 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____7056) in
            FStar_Parser_AST.Assume uu____7051 in
          decl'_to_decl se uu____7050 in
        FStar_Pervasives_Native.Some uu____7049
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____7058 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7058
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____7060 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7060
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____7069,t) ->
              let uu____7081 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7081
          | uu____7082 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7090,t) ->
              let uu____7102 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7102
          | uu____7103 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7127 -> failwith "Should not happen hopefully" in
        let uu____7136 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7136
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
        let uu____7146 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7146 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7156 = FStar_Options.print_implicits () in
               if uu____7156 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7165 =
               let uu____7166 =
                 let uu____7167 =
                   let uu____7180 =
                     let uu____7189 =
                       let uu____7196 =
                         let uu____7197 =
                           let uu____7210 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7210) in
                         FStar_Parser_AST.TyconAbbrev uu____7197 in
                       (uu____7196, FStar_Pervasives_Native.None) in
                     [uu____7189] in
                   (false, uu____7180) in
                 FStar_Parser_AST.Tycon uu____7167 in
               decl'_to_decl se uu____7166 in
             FStar_Pervasives_Native.Some uu____7165)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7238 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7238
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7242 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___79_7248  ->
                  match uu___79_7248 with
                  | FStar_Syntax_Syntax.Projector (uu____7249,uu____7250) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7251 -> true
                  | uu____7252 -> false)) in
        if uu____7242
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7257 =
               (let uu____7260 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7260) || (FStar_List.isEmpty uvs) in
             if uu____7257
             then resugar_term t
             else
               (let uu____7262 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7262 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7270 = resugar_term t1 in
                    label universes uu____7270) in
           let uu____7271 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7271)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7272 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7289 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7304 -> FStar_Pervasives_Native.None