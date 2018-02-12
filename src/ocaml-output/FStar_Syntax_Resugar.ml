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
                        let uu____2408 =
                          let uu____2409 =
                            let uu____2418 = resugar_body t11 in
                            (uu____2418, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2409 in
                        mk1 uu____2408
                    | uu____2421 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2476 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2506) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2512) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2597 -> (xs, pat, t1) in
             let resugar body =
               let uu____2608 =
                 let uu____2609 = FStar_Syntax_Subst.compress body in
                 uu____2609.FStar_Syntax_Syntax.n in
               match uu____2608 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2614) ->
                   let uu____2635 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2635 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2643 = FStar_Options.print_implicits () in
                          if uu____2643 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            ((map_opt ())
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2652 =
                          let uu____2661 =
                            let uu____2662 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2662.FStar_Syntax_Syntax.n in
                          match uu____2661 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let uu____2680 =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    let uu____2708 =
                                      FStar_List.map
                                        (fun es  ->
                                           FStar_All.pipe_right es
                                             (FStar_List.map
                                                (fun uu____2744  ->
                                                   match uu____2744 with
                                                   | (e2,uu____2750) ->
                                                       resugar_term e2)))
                                        pats in
                                    (uu____2708, body3)
                                | FStar_Syntax_Syntax.Meta_labeled (s,r,p) ->
                                    let uu____2758 =
                                      mk1
                                        (FStar_Parser_AST.Labeled
                                           (body3, s, p)) in
                                    ([], uu____2758)
                                | uu____2765 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (match uu____2680 with
                               | (pats,body4) -> (pats, body4))
                          | uu____2796 ->
                              let uu____2797 = resugar_term body2 in
                              ([], uu____2797) in
                        (match uu____2652 with
                         | (pats,body3) ->
                             let uu____2814 = uncurry xs3 pats body3 in
                             (match uu____2814 with
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
               | uu____2862 ->
                   if op = "forall"
                   then
                     let uu____2863 =
                       let uu____2864 =
                         let uu____2877 = resugar_term body in
                         ([], [[]], uu____2877) in
                       FStar_Parser_AST.QForall uu____2864 in
                     mk1 uu____2863
                   else
                     (let uu____2889 =
                        let uu____2890 =
                          let uu____2903 = resugar_term body in
                          ([], [[]], uu____2903) in
                        FStar_Parser_AST.QExists uu____2890 in
                      mk1 uu____2889) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2930)::[] -> resugar b
                | uu____2947 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2957) ->
             let uu____2962 = FStar_List.hd args1 in
             (match uu____2962 with | (e1,uu____2976) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____3021  ->
                       match uu____3021 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_39 when _0_39 = (Prims.parse_int "0") ->
                  let uu____3028 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____3028 with
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____3035 =
                         let uu____3036 =
                           let uu____3043 =
                             let uu____3046 = last1 args1 in
                             resugar uu____3046 in
                           (op1, uu____3043) in
                         FStar_Parser_AST.Op uu____3036 in
                       mk1 uu____3035
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____3061 =
                         let uu____3062 =
                           let uu____3069 =
                             let uu____3072 = last_two args1 in
                             resugar uu____3072 in
                           (op1, uu____3069) in
                         FStar_Parser_AST.Op uu____3062 in
                       mk1 uu____3061
                   | _0_42 when
                       (_0_42 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3087 =
                         let uu____3088 =
                           let uu____3095 =
                             let uu____3098 = last_three args1 in
                             resugar uu____3098 in
                           (op1, uu____3095) in
                         FStar_Parser_AST.Op uu____3088 in
                       mk1 uu____3087
                   | uu____3107 -> resugar_as_app e args1)
              | _0_43 when
                  (_0_43 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3114 =
                    let uu____3115 =
                      let uu____3122 =
                        let uu____3125 = last_two args1 in resugar uu____3125 in
                      (op1, uu____3122) in
                    FStar_Parser_AST.Op uu____3115 in
                  mk1 uu____3114
              | uu____3134 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3137,t1)::[]) ->
        let bnds =
          let uu____3218 =
            let uu____3231 =
              let uu____3236 = resugar_pat pat in
              let uu____3237 = resugar_term e in (uu____3236, uu____3237) in
            (FStar_Pervasives_Native.None, uu____3231) in
          [uu____3218] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3289,t1)::(pat2,uu____3292,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3388 =
          let uu____3389 =
            let uu____3396 = resugar_term e in
            let uu____3397 = resugar_term t1 in
            let uu____3398 = resugar_term t2 in
            (uu____3396, uu____3397, uu____3398) in
          FStar_Parser_AST.If uu____3389 in
        mk1 uu____3388
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3456 =
          match uu____3456 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3487 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3487 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3491 =
          let uu____3492 =
            let uu____3507 = resugar_term e in
            let uu____3508 = FStar_List.map resugar_branch branches in
            (uu____3507, uu____3508) in
          FStar_Parser_AST.Match uu____3492 in
        mk1 uu____3491
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3548) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3615 =
          let uu____3616 =
            let uu____3625 = resugar_term e in (uu____3625, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3616 in
        mk1 uu____3615
    | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3649 = FStar_Syntax_Subst.open_let_rec source_lbs body in
        (match uu____3649 with
         | (source_lbs1,body1) ->
             let resugar_one_binding bnd =
               let attrs_opt =
                 match bnd.FStar_Syntax_Syntax.lbattrs with
                 | [] -> FStar_Pervasives_Native.None
                 | tms ->
                     let uu____3700 = FStar_List.map resugar_term tms in
                     FStar_Pervasives_Native.Some uu____3700 in
               let uu____3705 =
                 let uu____3710 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3710 in
               match uu____3705 with
               | (univs1,td) ->
                   let uu____3729 =
                     let uu____3738 =
                       let uu____3739 = FStar_Syntax_Subst.compress td in
                       uu____3739.FStar_Syntax_Syntax.n in
                     match uu____3738 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3750,(t1,uu____3752)::(d,uu____3754)::[]) ->
                         (t1, d)
                     | uu____3797 -> failwith "wrong let binding format" in
                   (match uu____3729 with
                    | (typ,def) ->
                        let uu____3832 =
                          let uu____3839 =
                            let uu____3840 = FStar_Syntax_Subst.compress def in
                            uu____3840.FStar_Syntax_Syntax.n in
                          match uu____3839 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3851) ->
                              let uu____3872 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3872 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3886 =
                                       FStar_Options.print_implicits () in
                                     if uu____3886 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3888 -> ([], def, false) in
                        (match uu____3832 with
                         | (binders,term,is_pat_app) ->
                             let uu____3920 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3931 =
                                     let uu____3932 =
                                       let uu____3933 =
                                         let uu____3940 =
                                           bv_as_unique_ident bv in
                                         (uu____3940,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3933 in
                                     mk_pat uu____3932 in
                                   (uu____3931, term) in
                             (match uu____3920 with
                              | (pat,term1) ->
                                  let uu____3961 =
                                    if is_pat_app
                                    then
                                      let args =
                                        FStar_All.pipe_right binders
                                          ((map_opt ())
                                             (fun uu____3993  ->
                                                match uu____3993 with
                                                | (bv,q) ->
                                                    let uu____4008 =
                                                      resugar_arg_qual q in
                                                    FStar_Util.map_opt
                                                      uu____4008
                                                      (fun q1  ->
                                                         let uu____4020 =
                                                           let uu____4021 =
                                                             let uu____4028 =
                                                               bv_as_unique_ident
                                                                 bv in
                                                             (uu____4028, q1) in
                                                           FStar_Parser_AST.PatVar
                                                             uu____4021 in
                                                         mk_pat uu____4020))) in
                                      let uu____4031 =
                                        let uu____4036 = resugar_term term1 in
                                        ((mk_pat
                                            (FStar_Parser_AST.PatApp
                                               (pat, args))), uu____4036) in
                                      let uu____4039 =
                                        universe_to_string univs1 in
                                      (uu____4031, uu____4039)
                                    else
                                      (let uu____4045 =
                                         let uu____4050 = resugar_term term1 in
                                         (pat, uu____4050) in
                                       let uu____4051 =
                                         universe_to_string univs1 in
                                       (uu____4045, uu____4051)) in
                                  (attrs_opt, uu____3961)))) in
             let r = FStar_List.map resugar_one_binding source_lbs1 in
             let bnds =
               let f uu____4149 =
                 match uu____4149 with
                 | (attrs,(pb,univs1)) ->
                     let uu____4205 =
                       let uu____4206 = FStar_Options.print_universes () in
                       Prims.op_Negation uu____4206 in
                     if uu____4205
                     then (attrs, pb)
                     else
                       (attrs,
                         ((FStar_Pervasives_Native.fst pb),
                           (label univs1 (FStar_Pervasives_Native.snd pb)))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____4281) ->
        let s =
          let uu____4307 =
            let uu____4308 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____4308 FStar_Util.string_of_int in
          Prims.strcat "?u" uu____4307 in
        let uu____4309 = mk1 FStar_Parser_AST.Wild in label s uu____4309
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___72_4319 =
          match uu___72_4319 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4340 =
                  let uu____4341 = FStar_Syntax_Subst.compress h in
                  uu____4341.FStar_Syntax_Syntax.n in
                match uu____4340 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4361 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4361, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4384 = head_fv_universes_args h1 in
                    (match uu____4384 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4472 = head_fv_universes_args head1 in
                    (match uu____4472 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4544 ->
                    let uu____4545 =
                      let uu____4550 =
                        let uu____4551 =
                          let uu____4552 = resugar_term h in
                          parser_term_to_string uu____4552 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4551 in
                      (FStar_Errors.Fatal_NotApplicationOrFv, uu____4550) in
                    FStar_Errors.raise_error uu____4545
                      e.FStar_Syntax_Syntax.pos in
              let uu____4569 =
                try
                  let uu____4621 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4621
                with
                | FStar_Errors.Err uu____4642 ->
                    let uu____4647 =
                      let uu____4652 =
                        let uu____4653 =
                          let uu____4654 = resugar_term e in
                          parser_term_to_string uu____4654 in
                        FStar_Util.format1 "wrong Data_app head format %s"
                          uu____4653 in
                      (FStar_Errors.Fatal_WrongDataAppHeadFormat, uu____4652) in
                    FStar_Errors.raise_error uu____4647
                      e.FStar_Syntax_Syntax.pos in
              (match uu____4569 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4708 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4708, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.filter_map
                       (fun uu____4732  ->
                          match uu____4732 with
                          | (t1,q) ->
                              let uu____4751 = resugar_imp q in
                              (match uu____4751 with
                               | FStar_Pervasives_Native.Some rimp ->
                                   let uu____4761 =
                                     let uu____4766 = resugar_term t1 in
                                     (uu____4766, rimp) in
                                   FStar_Pervasives_Native.Some uu____4761
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None)) args in
                   let args2 =
                     let uu____4782 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4784 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4784) in
                     if uu____4782
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let
                    (uu____4807,(FStar_Pervasives_Native.None ,(p,t11))::[],t2)
                    -> mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4866 =
                      let uu____4867 =
                        let uu____4876 = resugar_seq t11 in
                        (uu____4876, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4867 in
                    mk1 uu____4866
                | uu____4879 -> t1 in
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
               | uu____4925 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4927 =
                let uu____4928 = FStar_Syntax_Subst.compress e in
                uu____4928.FStar_Syntax_Syntax.n in
              (match uu____4927 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4932;
                      FStar_Syntax_Syntax.vars = uu____4933;_},(term,uu____4935)::[])
                   -> resugar_term term
               | uu____4964 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____5002  ->
                       match uu____5002 with
                       | (x,uu____5008) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____5010,p) ->
             let uu____5012 =
               let uu____5013 =
                 let uu____5020 = resugar_term e in (uu____5020, l, p) in
               FStar_Parser_AST.Labeled uu____5013 in
             mk1 uu____5012
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____5022,s,uu____5024) ->
             (match e.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  mk1
                    (FStar_Parser_AST.Const
                       (FStar_Const.Const_string
                          ((Prims.strcat "(alien:" (Prims.strcat s ")")),
                            (e.FStar_Syntax_Syntax.pos))))
              | uu____5029 ->
                  (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                     (FStar_Errors.Warning_MetaAlienNotATmUnknown,
                       "Meta_alien was not a Tm_unknown");
                   resugar_term e))
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____5038 =
               let uu____5039 =
                 let uu____5048 = resugar_term e in
                 let uu____5049 =
                   let uu____5050 =
                     let uu____5051 =
                       let uu____5062 =
                         let uu____5069 =
                           let uu____5074 = resugar_term t1 in
                           (uu____5074, FStar_Parser_AST.Nothing) in
                         [uu____5069] in
                       (name1, uu____5062) in
                     FStar_Parser_AST.Construct uu____5051 in
                   mk1 uu____5050 in
                 (uu____5048, uu____5049, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____5039 in
             mk1 uu____5038
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5092,t1) ->
             let uu____5098 =
               let uu____5099 =
                 let uu____5108 = resugar_term e in
                 let uu____5109 =
                   let uu____5110 =
                     let uu____5111 =
                       let uu____5122 =
                         let uu____5129 =
                           let uu____5134 = resugar_term t1 in
                           (uu____5134, FStar_Parser_AST.Nothing) in
                         [uu____5129] in
                       (name1, uu____5122) in
                     FStar_Parser_AST.Construct uu____5111 in
                   mk1 uu____5110 in
                 (uu____5108, uu____5109, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____5099 in
             mk1 uu____5098)
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
             let uu____5182 = FStar_Options.print_universes () in
             if uu____5182
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
             let uu____5243 = FStar_Options.print_universes () in
             if uu____5243
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
          let uu____5284 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____5284, FStar_Parser_AST.Nothing) in
        let uu____5285 = FStar_Options.print_effect_args () in
        if uu____5285
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
                    let uu____5372 =
                      FStar_Syntax_Util.unthunk_lemma_post
                        (FStar_Pervasives_Native.fst post) in
                    (uu____5372, (FStar_Pervasives_Native.snd post)) in
                  let uu____5381 =
                    let uu____5390 =
                      FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                        (FStar_Pervasives_Native.fst pre) in
                    if uu____5390 then [] else [pre] in
                  let uu____5420 =
                    let uu____5429 =
                      let uu____5438 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid
                          (FStar_Pervasives_Native.fst pats) in
                      if uu____5438 then [] else [pats] in
                    FStar_List.append [post1] uu____5429 in
                  FStar_List.append uu____5381 uu____5420
              | uu____5492 -> c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5521  ->
                 match uu____5521 with
                 | (e,uu____5531) ->
                     let uu____5532 = resugar_term e in
                     (uu____5532, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___73_5553 =
            match uu___73_5553 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5586 = resugar_term e in
                       (uu____5586, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5591 -> aux l tl1) in
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
      let uu____5636 = b in
      match uu____5636 with
      | (x,aq) ->
          let uu____5641 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5641
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5655 =
                     let uu____5656 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5656 in
                   FStar_Parser_AST.mk_binder uu____5655 r
                     FStar_Parser_AST.Type_level imp
               | uu____5657 ->
                   let uu____5658 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5658
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5660 =
                        let uu____5661 =
                          let uu____5666 = bv_as_unique_ident x in
                          (uu____5666, e) in
                        FStar_Parser_AST.Annotated uu____5661 in
                      FStar_Parser_AST.mk_binder uu____5660 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5675 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5675 in
      let uu____5676 =
        let uu____5677 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5677.FStar_Syntax_Syntax.n in
      match uu____5676 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5685 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5685
          else
            (let uu____5687 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5687
               (fun aq  ->
                  let uu____5699 =
                    let uu____5700 =
                      let uu____5701 =
                        let uu____5708 = bv_as_unique_ident x in
                        (uu____5708, aq) in
                      FStar_Parser_AST.PatVar uu____5701 in
                    mk1 uu____5700 in
                  FStar_Pervasives_Native.Some uu____5699))
      | uu____5711 ->
          let uu____5712 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5712
            (fun aq  ->
               let pat =
                 let uu____5727 =
                   let uu____5728 =
                     let uu____5735 = bv_as_unique_ident x in
                     (uu____5735, aq) in
                   FStar_Parser_AST.PatVar uu____5728 in
                 mk1 uu____5727 in
               let uu____5738 = FStar_Options.print_bound_var_types () in
               if uu____5738
               then
                 let uu____5741 =
                   let uu____5742 =
                     let uu____5743 =
                       let uu____5748 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5748) in
                     FStar_Parser_AST.PatAscribed uu____5743 in
                   mk1 uu____5742 in
                 FStar_Pervasives_Native.Some uu____5741
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
              (fun uu____5825  ->
                 match uu____5825 with
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
              (fun uu____5860  ->
                 match uu____5860 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5867 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5867
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5873;
             FStar_Syntax_Syntax.fv_delta = uu____5874;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5901 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5901 FStar_List.rev in
          let args1 =
            let uu____5917 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5937  ->
                      match uu____5937 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5917 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____6007 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6007
            | (hd1::tl1,hd2::tl2) ->
                let uu____6030 = map21 tl1 tl2 in (hd1, hd2) :: uu____6030 in
          let args2 =
            let uu____6048 = map21 fields1 args1 in
            FStar_All.pipe_right uu____6048 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____6099  ->
                 match uu____6099 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____6109 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____6109 with
           | FStar_Pervasives_Native.Some (op,uu____6117) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____6126 =
                 let uu____6127 =
                   let uu____6134 = bv_as_unique_ident v1 in
                   let uu____6135 = to_arg_qual imp_opt in
                   (uu____6134, uu____6135) in
                 FStar_Parser_AST.PatVar uu____6127 in
               mk1 uu____6126)
      | FStar_Syntax_Syntax.Pat_wild uu____6140 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____6148 =
              let uu____6149 =
                let uu____6156 = bv_as_unique_ident bv in
                (uu____6156,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____6149 in
            mk1 uu____6148 in
          let uu____6159 = FStar_Options.print_bound_var_types () in
          if uu____6159
          then
            let uu____6160 =
              let uu____6161 =
                let uu____6166 = resugar_term term in (pat, uu____6166) in
              FStar_Parser_AST.PatAscribed uu____6161 in
            mk1 uu____6160
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___74_6172  ->
    match uu___74_6172 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6181 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6182 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6183 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6188 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6197 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6206 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___75_6209  ->
    match uu___75_6209 with
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
          (tylid,uvs,bs,t,uu____6236,datacons) ->
          let uu____6246 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____6273,uu____6274,uu____6275,inductive_lid,uu____6277,uu____6278)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____6283 -> failwith "unexpected")) in
          (match uu____6246 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____6302 = FStar_Options.print_implicits () in
                 if uu____6302 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   ((map_opt ())
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____6312 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___76_6317  ->
                           match uu___76_6317 with
                           | FStar_Syntax_Syntax.RecordType uu____6318 ->
                               true
                           | uu____6327 -> false)) in
                 if uu____6312
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____6375,univs1,term,uu____6378,num,uu____6380)
                         ->
                         let uu____6385 =
                           let uu____6386 = FStar_Syntax_Subst.compress term in
                           uu____6386.FStar_Syntax_Syntax.n in
                         (match uu____6385 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6400) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6461  ->
                                        match uu____6461 with
                                        | (b,qual) ->
                                            let uu____6476 =
                                              let uu____6477 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6477 in
                                            let uu____6478 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6476, uu____6478,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6489 -> failwith "unexpected")
                     | uu____6500 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6621,num,uu____6623) ->
                          let c =
                            let uu____6641 =
                              let uu____6644 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6644 in
                            ((l.FStar_Ident.ident), uu____6641,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6661 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6737 ->
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
        let uu____6755 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6755;
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
      let uu____6768 = ts in
      match uu____6768 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6776 =
            let uu____6777 =
              let uu____6790 =
                let uu____6799 =
                  let uu____6806 =
                    let uu____6807 =
                      let uu____6820 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6820) in
                    FStar_Parser_AST.TyconAbbrev uu____6807 in
                  (uu____6806, FStar_Pervasives_Native.None) in
                [uu____6799] in
              (false, uu____6790) in
            FStar_Parser_AST.Tycon uu____6777 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6776
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
            let uu____6874 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6874 with
            | (bs,action_defn) ->
                let uu____6881 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6881 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6889 = FStar_Options.print_implicits () in
                       if uu____6889
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6894 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6894 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6908 =
                           let uu____6919 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6919,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6908 in
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
          let uu____6993 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6993 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____7001 = FStar_Options.print_implicits () in
                if uu____7001 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____7006 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____7006 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7063) ->
        let uu____7072 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____7094 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____7111 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____7118 -> false
                  | uu____7133 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____7072 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____7165 se1 =
               match uu____7165 with
               | (datacon_ses1,tycons) ->
                   let uu____7191 = resugar_typ datacon_ses1 se1 in
                   (match uu____7191 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____7206 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____7206 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____7241 =
                         let uu____7242 =
                           let uu____7243 =
                             let uu____7256 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____7256) in
                           FStar_Parser_AST.Tycon uu____7243 in
                         decl'_to_decl se uu____7242 in
                       FStar_Pervasives_Native.Some uu____7241
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____7287,uu____7288,uu____7289,uu____7290,uu____7291)
                            ->
                            let uu____7296 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____7296
                        | uu____7299 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____7302 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____7308) ->
        let uu____7313 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___77_7319  ->
                  match uu___77_7319 with
                  | FStar_Syntax_Syntax.Projector (uu____7320,uu____7321) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7322 -> true
                  | uu____7323 -> false)) in
        if uu____7313
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____7346) ->
               let uu____7375 =
                 let uu____7376 =
                   let uu____7377 =
                     let uu____7388 =
                       FStar_List.map FStar_Pervasives_Native.snd lets in
                     (isrec, uu____7388) in
                   FStar_Parser_AST.TopLevelLet uu____7377 in
                 decl'_to_decl se uu____7376 in
               FStar_Pervasives_Native.Some uu____7375
           | uu____7425 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____7429,fml) ->
        let uu____7431 =
          let uu____7432 =
            let uu____7433 =
              let uu____7438 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____7438) in
            FStar_Parser_AST.Assume uu____7433 in
          decl'_to_decl se uu____7432 in
        FStar_Pervasives_Native.Some uu____7431
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____7440 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7440
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____7442 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7442
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____7451,t) ->
              let uu____7463 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7463
          | uu____7464 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7472,t) ->
              let uu____7484 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7484
          | uu____7485 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7509 -> failwith "Should not happen hopefully" in
        let uu____7518 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7518
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
        let uu____7528 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7528 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7538 = FStar_Options.print_implicits () in
               if uu____7538 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 ((map_opt ())
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7547 =
               let uu____7548 =
                 let uu____7549 =
                   let uu____7562 =
                     let uu____7571 =
                       let uu____7578 =
                         let uu____7579 =
                           let uu____7592 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7592) in
                         FStar_Parser_AST.TyconAbbrev uu____7579 in
                       (uu____7578, FStar_Pervasives_Native.None) in
                     [uu____7571] in
                   (false, uu____7562) in
                 FStar_Parser_AST.Tycon uu____7549 in
               decl'_to_decl se uu____7548 in
             FStar_Pervasives_Native.Some uu____7547)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7620 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7620
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7624 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___78_7630  ->
                  match uu___78_7630 with
                  | FStar_Syntax_Syntax.Projector (uu____7631,uu____7632) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7633 -> true
                  | uu____7634 -> false)) in
        if uu____7624
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7639 =
               (let uu____7642 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7642) || (FStar_List.isEmpty uvs) in
             if uu____7639
             then resugar_term t
             else
               (let uu____7644 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7644 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7652 = resugar_term t1 in
                    label universes uu____7652) in
           let uu____7653 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7653)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7654 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7671 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7686 -> FStar_Pervasives_Native.None