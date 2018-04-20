open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1 ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t ->
    let uu____7 = FStar_Parser_ToDocument.term_to_document t in
    doc_to_string uu____7
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t ->
    let uu____11 = FStar_Parser_ToDocument.pat_to_document t in
    doc_to_string uu____11
let map_opt :
  'Auu____16 'Auu____17 .
    Prims.unit ->
      ('Auu____16 -> 'Auu____17 FStar_Pervasives_Native.option) ->
        'Auu____16 Prims.list -> 'Auu____17 Prims.list
  = fun uu____31 -> FStar_List.filter_map
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x ->
    let unique_name =
      let uu____36 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ()) in
      if uu____36
      then
        let uu____37 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____37
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp :
  'Auu____41 .
    ('Auu____41,
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____41,
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___68_95 ->
            match uu___68_95 with
            | (uu____102, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____103)) -> false
            | uu____106 -> true))
let filter_pattern_imp :
  'Auu____115 .
    ('Auu____115, Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____115, Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun xs ->
    FStar_List.filter
      (fun uu____145 ->
         match uu____145 with
         | (uu____150, is_implicit1) -> Prims.op_Negation is_implicit1) xs
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s ->
    fun t ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
let (resugar_arg_qual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  =
  fun q ->
    match q with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
        if b
        then FStar_Pervasives_Native.None
        else
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
let (resugar_imp :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.imp)
  =
  fun q ->
    match q with
    | FStar_Pervasives_Native.None -> FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) ->
        FStar_Parser_AST.Hash
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
        FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) ->
        FStar_Parser_AST.Nothing
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int, FStar_Syntax_Syntax.universe)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1 ->
    fun u ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____214 -> (n1, u)
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1 ->
    let uu____222 = FStar_Options.print_universes () in
    if uu____222
    then
      let uu____223 = FStar_List.map (fun x -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____223 (FStar_String.concat ", ")
    else ""
let rec (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env -> fun u -> fun r -> resugar_universe u r
and (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u ->
    fun r ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____263 ->
          let uu____264 = universe_to_int (Prims.parse_int "0") u in
          (match uu____264 with
           | (n1, u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero ->
                    let uu____271 =
                      let uu____272 =
                        let uu____273 =
                          let uu____284 = FStar_Util.string_of_int n1 in
                          (uu____284, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____273 in
                      FStar_Parser_AST.Const uu____272 in
                    mk1 uu____271 r
                | uu____295 ->
                    let e1 =
                      let uu____297 =
                        let uu____298 =
                          let uu____299 =
                            let uu____310 = FStar_Util.string_of_int n1 in
                            (uu____310, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____299 in
                        FStar_Parser_AST.Const uu____298 in
                      mk1 uu____297 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____327 ->
               let t =
                 let uu____331 =
                   let uu____332 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____332 in
                 mk1 uu____331 r in
               FStar_List.fold_left
                 (fun acc ->
                    fun x ->
                      let uu____338 =
                        let uu____339 =
                          let uu____346 = resugar_universe x r in
                          (acc, uu____346, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____339 in
                      mk1 uu____338 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____348 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____359 =
              let uu____364 =
                let uu____365 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____365 in
              (uu____364, r) in
            FStar_Ident.mk_ident uu____359 in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown -> mk1 FStar_Parser_AST.Wild r
let (string_to_op :
  Prims.string ->
    (Prims.string, Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun s ->
    let name_of_op uu___69_388 =
      match uu___69_388 with
      | "Amp" ->
          FStar_Pervasives_Native.Some ("&", FStar_Pervasives_Native.None)
      | "At" ->
          FStar_Pervasives_Native.Some ("@", FStar_Pervasives_Native.None)
      | "Plus" ->
          FStar_Pervasives_Native.Some ("+", FStar_Pervasives_Native.None)
      | "Minus" ->
          FStar_Pervasives_Native.Some ("-", FStar_Pervasives_Native.None)
      | "Subtraction" ->
          FStar_Pervasives_Native.Some
            ("-", (FStar_Pervasives_Native.Some (Prims.parse_int "2")))
      | "Tilde" ->
          FStar_Pervasives_Native.Some ("~", FStar_Pervasives_Native.None)
      | "Slash" ->
          FStar_Pervasives_Native.Some ("/", FStar_Pervasives_Native.None)
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", FStar_Pervasives_Native.None)
      | "Less" ->
          FStar_Pervasives_Native.Some ("<", FStar_Pervasives_Native.None)
      | "Equals" ->
          FStar_Pervasives_Native.Some ("=", FStar_Pervasives_Native.None)
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", FStar_Pervasives_Native.None)
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", FStar_Pervasives_Native.None)
      | "Bar" ->
          FStar_Pervasives_Native.Some ("|", FStar_Pervasives_Native.None)
      | "Bang" ->
          FStar_Pervasives_Native.Some ("!", FStar_Pervasives_Native.None)
      | "Hat" ->
          FStar_Pervasives_Native.Some ("^", FStar_Pervasives_Native.None)
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", FStar_Pervasives_Native.None)
      | "Star" ->
          FStar_Pervasives_Native.Some ("*", FStar_Pervasives_Native.None)
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", FStar_Pervasives_Native.None)
      | "Colon" ->
          FStar_Pervasives_Native.Some (":", FStar_Pervasives_Native.None)
      | "Dollar" ->
          FStar_Pervasives_Native.Some ("$", FStar_Pervasives_Native.None)
      | "Dot" ->
          FStar_Pervasives_Native.Some (".", FStar_Pervasives_Native.None)
      | uu____565 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____612 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____624 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____624 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____634 ->
               let op =
                 let uu____638 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc ->
                      fun x ->
                        match x with
                        | FStar_Pervasives_Native.Some (op, uu____680) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None ->
                            failwith "wrong composed operator format") ""
                   uu____638 in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
type expected_arity = Prims.int FStar_Pervasives_Native.option[@@deriving
                                                                show]
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string, expected_arity) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun t ->
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
      let uu____884 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____884 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____938 ->
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
          then
            FStar_Pervasives_Native.Some
              ("dtuple", FStar_Pervasives_Native.None)
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some
                ("tuple", FStar_Pervasives_Native.None)
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", FStar_Pervasives_Native.None)
              else
                (let uu____1009 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____1009
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None) in
    let uu____1033 =
      let uu____1034 = FStar_Syntax_Subst.compress t in
      uu____1034.FStar_Syntax_Syntax.n in
    match uu____1033 with
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
        let uu____1057 = string_to_op s in
        (match uu____1057 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1091 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e, us) -> resugar_term_as_op e
    | uu____1106 -> FStar_Pervasives_Native.None
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) ->
        true
    | uu____1114 -> false
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1118 -> true
    | uu____1119 -> false
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1126 ->
        let uu____1127 = is_tuple_constructor_lid lid in
        Prims.op_Negation uu____1127
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid) =
  fun env ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____1135 = may_shorten lid in
      if uu____1135 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env ->
    fun t ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un in
      let name a r =
        let uu____1204 = FStar_Ident.lid_of_path [a] r in
        FStar_Parser_AST.Name uu____1204 in
      let uu____1205 =
        let uu____1206 = FStar_Syntax_Subst.compress t in
        uu____1206.FStar_Syntax_Syntax.n in
      match uu____1205 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1209 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1235 = FStar_Syntax_Util.unfold_lazy i in
          resugar_term' env uu____1235
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1238 =
              let uu____1241 = bv_as_unique_ident x in [uu____1241] in
            FStar_Ident.lid_of_ids uu____1238 in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1244 =
              let uu____1247 = bv_as_unique_ident x in [uu____1247] in
            FStar_Ident.lid_of_ids uu____1244 in
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
            let uu____1265 =
              let uu____1266 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
              FStar_Parser_AST.Discrim uu____1266 in
            mk1 uu____1265
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
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
               | uu____1276 -> failwith "wrong projector format")
            else
              (let uu____1280 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1283 =
                      let uu____1285 =
                        FStar_String.get s (Prims.parse_int "0") in
                      FStar_Char.uppercase uu____1285 in
                    let uu____1287 = FStar_String.get s (Prims.parse_int "0") in
                    uu____1283 <> uu____1287) in
               if uu____1280
               then
                 let uu____1290 =
                   let uu____1291 = maybe_shorten_fv env fv in
                   FStar_Parser_AST.Var uu____1291 in
                 mk1 uu____1290
               else
                 (let uu____1293 =
                    let uu____1294 =
                      let uu____1305 = maybe_shorten_fv env fv in
                      (uu____1305, []) in
                    FStar_Parser_AST.Construct uu____1294 in
                  mk1 uu____1293))
      | FStar_Syntax_Syntax.Tm_uinst (e, universes) ->
          let e1 = resugar_term' env e in
          let uu____1323 = FStar_Options.print_universes () in
          if uu____1323
          then
            let univs1 =
              FStar_List.map
                (fun x -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes in
            (match e1 with
             | {
                 FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1, args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____1352 =
                     FStar_List.map (fun u -> (u, FStar_Parser_AST.UnivApp))
                       univs1 in
                   FStar_List.append args uu____1352 in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1375 ->
                 FStar_List.fold_left
                   (fun acc ->
                      fun u ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1382 = FStar_Syntax_Syntax.is_teff t in
          if uu____1382
          then
            let uu____1383 = name "Effect" t.FStar_Syntax_Syntax.pos in
            mk1 uu____1383
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1386 =
            match u with
            | FStar_Syntax_Syntax.U_zero -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown -> ("Type", false)
            | uu____1395 -> ("Type", true) in
          (match uu____1386 with
           | (nm, needs_app) ->
               let typ =
                 let uu____1399 = name nm t.FStar_Syntax_Syntax.pos in
                 mk1 uu____1399 in
               let uu____1400 =
                 needs_app && (FStar_Options.print_universes ()) in
               if uu____1400
               then
                 let uu____1401 =
                   let uu____1402 =
                     let uu____1409 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos in
                     (typ, uu____1409, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1402 in
                 mk1 uu____1401
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs, body, uu____1413) ->
          let uu____1434 = FStar_Syntax_Subst.open_term xs body in
          (match uu____1434 with
           | (xs1, body1) ->
               let xs2 =
                 let uu____1442 = FStar_Options.print_implicits () in
                 if uu____1442 then xs1 else filter_imp xs1 in
               let body_bv = FStar_Syntax_Free.names body1 in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1459 ->
                         match uu____1459 with
                         | (x, qual) -> resugar_bv_as_pat env x qual body_bv)) in
               let body2 = resugar_term' env body1 in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs, body) ->
          let uu____1489 = FStar_Syntax_Subst.open_comp xs body in
          (match uu____1489 with
           | (xs1, body1) ->
               let xs2 =
                 let uu____1497 = FStar_Options.print_implicits () in
                 if uu____1497 then xs1 else filter_imp xs1 in
               let body2 = resugar_comp' env body1 in
               let xs3 =
                 let uu____1503 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos)) in
                 FStar_All.pipe_right uu____1503 FStar_List.rev in
               let rec aux body3 uu___70_1522 =
                 match uu___70_1522 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                     aux body4 tl1 in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu____1538 =
            let uu____1543 =
              let uu____1544 = FStar_Syntax_Syntax.mk_binder x in
              [uu____1544] in
            FStar_Syntax_Subst.open_term uu____1543 phi in
          (match uu____1538 with
           | (x1, phi1) ->
               let b =
                 let uu____1548 =
                   let uu____1551 = FStar_List.hd x1 in
                   resugar_binder' env uu____1551 t.FStar_Syntax_Syntax.pos in
                 FStar_Util.must uu____1548 in
               let uu____1556 =
                 let uu____1557 =
                   let uu____1562 = resugar_term' env phi1 in (b, uu____1562) in
                 FStar_Parser_AST.Refine uu____1557 in
               mk1 uu____1556)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1564;
             FStar_Syntax_Syntax.vars = uu____1565;_},
           (e, uu____1567)::[])
          when
          (let uu____1598 = FStar_Options.print_implicits () in
           Prims.op_Negation uu____1598) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2p_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1600;
             FStar_Syntax_Syntax.vars = uu____1601;_},
           (t_base, uu____1603)::(f, uu____1605)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid ->
          let uu____1644 =
            let uu____1645 = FStar_Syntax_Subst.compress f in
            uu____1645.FStar_Syntax_Syntax.n in
          (match uu____1644 with
           | FStar_Syntax_Syntax.Tm_abs (x::[], f1, uu____1650) ->
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_refine
                      ((FStar_Pervasives_Native.fst x), f1))
                   FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
               resugar_term' env t1
           | uu____1682 ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                   t_base in
               let phi =
                 let uu____1687 =
                   let uu____1688 =
                     let uu____1689 =
                       let uu____1690 = FStar_Syntax_Syntax.bv_to_name x in
                       FStar_Syntax_Syntax.as_arg uu____1690 in
                     [uu____1689] in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1688 in
                 uu____1687 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos in
               let uu____1693 = FStar_Syntax_Util.refine x phi in
               resugar_term' env uu____1693)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____1695;
                  FStar_Syntax_Syntax.vars = uu____1696;_},
                uu____1697);
             FStar_Syntax_Syntax.pos = uu____1698;
             FStar_Syntax_Syntax.vars = uu____1699;_},
           (t_base, uu____1701)::(f, uu____1703)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid ->
          let uu____1746 =
            let uu____1747 = FStar_Syntax_Subst.compress f in
            uu____1747.FStar_Syntax_Syntax.n in
          (match uu____1746 with
           | FStar_Syntax_Syntax.Tm_abs (x::[], f1, uu____1752) ->
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_refine
                      ((FStar_Pervasives_Native.fst x), f1))
                   FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
               resugar_term' env t1
           | uu____1784 ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                   t_base in
               let phi =
                 let uu____1789 =
                   let uu____1790 =
                     let uu____1791 =
                       let uu____1792 = FStar_Syntax_Syntax.bv_to_name x in
                       FStar_Syntax_Syntax.as_arg uu____1792 in
                     [uu____1791] in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1790 in
                 uu____1789 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos in
               let uu____1795 = FStar_Syntax_Util.refine x phi in
               resugar_term' env uu____1795)
      | FStar_Syntax_Syntax.Tm_app (e, args) ->
          let rec last1 uu___71_1837 =
            match uu___71_1837 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1907 -> failwith "last of an empty list" in
          let rec last_two uu___72_1943 =
            match uu___72_1943 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1974::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2051::t1 -> last_two t1 in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2118 ->
                   match uu____2118 with
                   | (e2, qual) ->
                       let uu____2135 = resugar_term' env e2 in
                       let uu____2136 = resugar_imp qual in
                       (uu____2135, uu____2136)) args1 in
            let uu____2137 = resugar_term' env e1 in
            match uu____2137 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd1, previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd1, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc ->
                     fun uu____2174 ->
                       match uu____2174 with
                       | (x, qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2 in
          let args1 =
            let uu____2190 = FStar_Options.print_implicits () in
            if uu____2190 then args else filter_imp args in
          let uu____2202 = resugar_term_as_op e in
          (match uu____2202 with
           | FStar_Pervasives_Native.None -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple", uu____2213) ->
               (match args1 with
                | (fst1, uu____2219)::(snd1, uu____2221)::rest ->
                    let e1 =
                      let uu____2252 =
                        let uu____2253 =
                          let uu____2260 =
                            let uu____2263 = resugar_term' env fst1 in
                            let uu____2264 =
                              let uu____2267 = resugar_term' env snd1 in
                              [uu____2267] in
                            uu____2263 :: uu____2264 in
                          ((FStar_Ident.id_of_text "*"), uu____2260) in
                        FStar_Parser_AST.Op uu____2253 in
                      mk1 uu____2252 in
                    FStar_List.fold_left
                      (fun acc ->
                         fun uu____2280 ->
                           match uu____2280 with
                           | (x, uu____2286) ->
                               let uu____2287 =
                                 let uu____2288 =
                                   let uu____2295 =
                                     let uu____2298 =
                                       let uu____2301 = resugar_term' env x in
                                       [uu____2301] in
                                     e1 :: uu____2298 in
                                   ((FStar_Ident.id_of_text "*"), uu____2295) in
                                 FStar_Parser_AST.Op uu____2288 in
                               mk1 uu____2287) e1 rest
                | uu____2304 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple", uu____2313) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1 in
               let body =
                 match args2 with
                 | (b, uu____2339)::[] -> b
                 | uu____2356 -> failwith "wrong arguments to dtuple" in
               let uu____2367 =
                 let uu____2368 = FStar_Syntax_Subst.compress body in
                 uu____2368.FStar_Syntax_Syntax.n in
               (match uu____2367 with
                | FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2373) ->
                    let uu____2394 = FStar_Syntax_Subst.open_term xs body1 in
                    (match uu____2394 with
                     | (xs1, body2) ->
                         let xs2 =
                           let uu____2402 = FStar_Options.print_implicits () in
                           if uu____2402 then xs1 else filter_imp xs1 in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos)) in
                         let body3 = resugar_term' env body2 in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2414 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2435 ->
                              match uu____2435 with
                              | (e1, qual) -> resugar_term' env e1)) in
                    let e1 = resugar_term' env e in
                    FStar_List.fold_left
                      (fun acc ->
                         fun x ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple", uu____2447) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read, uu____2453) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2458 = FStar_List.hd args1 in
               (match uu____2458 with
                | (t1, uu____2472) ->
                    let uu____2477 =
                      let uu____2478 = FStar_Syntax_Subst.compress t1 in
                      uu____2478.FStar_Syntax_Syntax.n in
                    (match uu____2477 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos in
                         let uu____2483 =
                           let uu____2484 =
                             let uu____2489 = resugar_term' env t1 in
                             (uu____2489, f) in
                           FStar_Parser_AST.Project uu____2484 in
                         mk1 uu____2483
                     | uu____2490 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with", uu____2491) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1 in
               let uu____2511 =
                 match new_args with
                 | (a1, uu____2529)::(a2, uu____2531)::[] -> (a1, a2)
                 | uu____2562 -> failwith "wrong arguments to try_with" in
               (match uu____2511 with
                | (body, handler) ->
                    let decomp term =
                      let uu____2593 =
                        let uu____2594 = FStar_Syntax_Subst.compress term in
                        uu____2594.FStar_Syntax_Syntax.n in
                      match uu____2593 with
                      | FStar_Syntax_Syntax.Tm_abs (x, e1, uu____2599) ->
                          let uu____2620 = FStar_Syntax_Subst.open_term x e1 in
                          (match uu____2620 with | (x1, e2) -> e2)
                      | uu____2627 ->
                          failwith "wrong argument format to try_with" in
                    let body1 =
                      let uu____2629 = decomp body in
                      resugar_term' env uu____2629 in
                    let handler1 =
                      let uu____2631 = decomp handler in
                      resugar_term' env uu____2631 in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1, (uu____2637, uu____2638, b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2670, uu____2671, b) -> b
                      | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                          let uu____2708 =
                            let uu____2709 =
                              let uu____2718 = resugar_body t11 in
                              (uu____2718, t2, t3) in
                            FStar_Parser_AST.Ascribed uu____2709 in
                          mk1 uu____2708
                      | uu____2721 ->
                          failwith "unexpected body format to try_with" in
                    let e1 = resugar_body body1 in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2, branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                          resugar_branches t11
                      | uu____2776 -> [] in
                    let branches = resugar_branches handler1 in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with", uu____2806) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op, uu____2812) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x, p, body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x, p, body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2897 -> (xs, pat, t1) in
               let resugar body =
                 let uu____2908 =
                   let uu____2909 = FStar_Syntax_Subst.compress body in
                   uu____2909.FStar_Syntax_Syntax.n in
                 match uu____2908 with
                 | FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2914) ->
                     let uu____2935 = FStar_Syntax_Subst.open_term xs body1 in
                     (match uu____2935 with
                      | (xs1, body2) ->
                          let xs2 =
                            let uu____2943 = FStar_Options.print_implicits () in
                            if uu____2943 then xs1 else filter_imp xs1 in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos)) in
                          let uu____2952 =
                            let uu____2961 =
                              let uu____2962 =
                                FStar_Syntax_Subst.compress body2 in
                              uu____2962.FStar_Syntax_Syntax.n in
                            match uu____2961 with
                            | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
                                let body3 = resugar_term' env e1 in
                                let uu____2980 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____3008 =
                                        FStar_List.map
                                          (fun es ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3044 ->
                                                     match uu____3044 with
                                                     | (e2, uu____3050) ->
                                                         resugar_term' env e2)))
                                          pats in
                                      (uu____3008, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled
                                      (s, r, p) ->
                                      let uu____3058 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p)) in
                                      ([], uu____3058)
                                  | uu____3065 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists" in
                                (match uu____2980 with
                                 | (pats, body4) -> (pats, body4))
                            | uu____3096 ->
                                let uu____3097 = resugar_term' env body2 in
                                ([], uu____3097) in
                          (match uu____2952 with
                           | (pats, body3) ->
                               let uu____3114 = uncurry xs3 pats body3 in
                               (match uu____3114 with
                                | (xs4, pats1, body4) ->
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
                 | uu____3162 ->
                     if op = "forall"
                     then
                       let uu____3163 =
                         let uu____3164 =
                           let uu____3177 = resugar_term' env body in
                           ([], [[]], uu____3177) in
                         FStar_Parser_AST.QForall uu____3164 in
                       mk1 uu____3163
                     else
                       (let uu____3189 =
                          let uu____3190 =
                            let uu____3203 = resugar_term' env body in
                            ([], [[]], uu____3203) in
                          FStar_Parser_AST.QExists uu____3190 in
                        mk1 uu____3189) in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1 in
                 (match args2 with
                  | (b, uu____3230)::[] -> resugar b
                  | uu____3247 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc", uu____3257) ->
               let uu____3262 = FStar_List.hd args1 in
               (match uu____3262 with
                | (e1, uu____3276) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op, expected_arity) ->
               let op1 = FStar_Ident.id_of_text op in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3343 ->
                         match uu____3343 with
                         | (e1, qual) ->
                             let uu____3360 = resugar_term' env e1 in
                             let uu____3361 = resugar_imp qual in
                             (uu____3360, uu____3361))) in
               (match expected_arity with
                | FStar_Pervasives_Native.None ->
                    let resugared_args = resugar args1 in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1 in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3374 =
                        FStar_Util.first_N expect_n resugared_args in
                      (match uu____3374 with
                       | (op_args, rest) ->
                           let head1 =
                             let uu____3422 =
                               let uu____3423 =
                                 let uu____3430 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args in
                                 (op1, uu____3430) in
                               FStar_Parser_AST.Op uu____3423 in
                             mk1 uu____3422 in
                           FStar_List.fold_left
                             (fun head2 ->
                                fun uu____3448 ->
                                  match uu____3448 with
                                  | (arg, qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3463 =
                      let uu____3464 =
                        let uu____3471 =
                          let uu____3474 = resugar args1 in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3474 in
                        (op1, uu____3471) in
                      FStar_Parser_AST.Op uu____3464 in
                    mk1 uu____3463
                | uu____3487 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e, (pat, wopt, t1)::[]) ->
          let uu____3556 = FStar_Syntax_Subst.open_branch (pat, wopt, t1) in
          (match uu____3556 with
           | (pat1, wopt1, t2) ->
               let branch_bv = FStar_Syntax_Free.names t2 in
               let bnds =
                 let uu____3602 =
                   let uu____3615 =
                     let uu____3620 = resugar_pat' env pat1 branch_bv in
                     let uu____3621 = resugar_term' env e in
                     (uu____3620, uu____3621) in
                   (FStar_Pervasives_Native.None, uu____3615) in
                 [uu____3602] in
               let body = resugar_term' env t2 in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e, (pat1, uu____3673, t1)::(pat2, uu____3676, t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3772 =
            let uu____3773 =
              let uu____3780 = resugar_term' env e in
              let uu____3781 = resugar_term' env t1 in
              let uu____3782 = resugar_term' env t2 in
              (uu____3780, uu____3781, uu____3782) in
            FStar_Parser_AST.If uu____3773 in
          mk1 uu____3772
      | FStar_Syntax_Syntax.Tm_match (e, branches) ->
          let resugar_branch uu____3846 =
            match uu____3846 with
            | (pat, wopt, b) ->
                let uu____3888 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b) in
                (match uu____3888 with
                 | (pat1, wopt1, b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1 in
                     let pat2 = resugar_pat' env pat1 branch_bv in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3940 = resugar_term' env e1 in
                           FStar_Pervasives_Native.Some uu____3940 in
                     let b2 = resugar_term' env b1 in (pat2, wopt2, b2)) in
          let uu____3944 =
            let uu____3945 =
              let uu____3960 = resugar_term' env e in
              let uu____3961 = FStar_List.map resugar_branch branches in
              (uu____3960, uu____3961) in
            FStar_Parser_AST.Match uu____3945 in
          mk1 uu____3944
      | FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____4007) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1 in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt in
          let uu____4074 =
            let uu____4075 =
              let uu____4084 = resugar_term' env e in
              (uu____4084, term, tac_opt1) in
            FStar_Parser_AST.Ascribed uu____4075 in
          mk1 uu____4074
      | FStar_Syntax_Syntax.Tm_let ((is_rec, source_lbs), body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
          let uu____4108 = FStar_Syntax_Subst.open_let_rec source_lbs body in
          (match uu____4108 with
           | (source_lbs1, body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4159 =
                         FStar_List.map (resugar_term' env) tms in
                       FStar_Pervasives_Native.Some uu____4159 in
                 let uu____4164 =
                   let uu____4169 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4169 in
                 match uu____4164 with
                 | (univs1, td) ->
                     let uu____4188 =
                       let uu____4197 =
                         let uu____4198 = FStar_Syntax_Subst.compress td in
                         uu____4198.FStar_Syntax_Syntax.n in
                       match uu____4197 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4209,
                            (t1, uu____4211)::(d, uu____4213)::[])
                           -> (t1, d)
                       | uu____4256 -> failwith "wrong let binding format" in
                     (match uu____4188 with
                      | (typ, def) ->
                          let uu____4291 =
                            let uu____4298 =
                              let uu____4299 =
                                FStar_Syntax_Subst.compress def in
                              uu____4299.FStar_Syntax_Syntax.n in
                            match uu____4298 with
                            | FStar_Syntax_Syntax.Tm_abs (b, t1, uu____4310)
                                ->
                                let uu____4331 =
                                  FStar_Syntax_Subst.open_term b t1 in
                                (match uu____4331 with
                                 | (b1, t2) ->
                                     let b2 =
                                       let uu____4345 =
                                         FStar_Options.print_implicits () in
                                       if uu____4345
                                       then b1
                                       else filter_imp b1 in
                                     (b2, t2, true))
                            | uu____4347 -> ([], def, false) in
                          (match uu____4291 with
                           | (binders, term, is_pat_app) ->
                               let uu____4379 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4390 =
                                       let uu____4391 =
                                         let uu____4392 =
                                           let uu____4399 =
                                             bv_as_unique_ident bv in
                                           (uu____4399,
                                             FStar_Pervasives_Native.None) in
                                         FStar_Parser_AST.PatVar uu____4392 in
                                       mk_pat uu____4391 in
                                     (uu____4390, term) in
                               (match uu____4379 with
                                | (pat, term1) ->
                                    let uu____4420 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4452 ->
                                                  match uu____4452 with
                                                  | (bv, q) ->
                                                      let uu____4467 =
                                                        resugar_arg_qual q in
                                                      FStar_Util.map_opt
                                                        uu____4467
                                                        (fun q1 ->
                                                           let uu____4479 =
                                                             let uu____4480 =
                                                               let uu____4487
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv in
                                                               (uu____4487,
                                                                 q1) in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4480 in
                                                           mk_pat uu____4479))) in
                                        let uu____4490 =
                                          let uu____4495 =
                                            resugar_term' env term1 in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4495) in
                                        let uu____4498 =
                                          universe_to_string univs1 in
                                        (uu____4490, uu____4498)
                                      else
                                        (let uu____4504 =
                                           let uu____4509 =
                                             resugar_term' env term1 in
                                           (pat, uu____4509) in
                                         let uu____4510 =
                                           universe_to_string univs1 in
                                         (uu____4504, uu____4510)) in
                                    (attrs_opt, uu____4420)))) in
               let r = FStar_List.map resugar_one_binding source_lbs1 in
               let bnds =
                 let f uu____4608 =
                   match uu____4608 with
                   | (attrs, (pb, univs1)) ->
                       let uu____4664 =
                         let uu____4665 = FStar_Options.print_universes () in
                         Prims.op_Negation uu____4665 in
                       if uu____4664
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs1 (FStar_Pervasives_Native.snd pb)))) in
                 FStar_List.map f r in
               let body2 = resugar_term' env body1 in
               mk1
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u, uu____4740) ->
          let s =
            let uu____4766 =
              let uu____4767 = FStar_Syntax_Unionfind.uvar_id u in
              FStar_All.pipe_right uu____4767 FStar_Util.string_of_int in
            Prims.strcat "?u" uu____4766 in
          let uu____4768 = mk1 FStar_Parser_AST.Wild in label s uu____4768
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic -> FStar_Parser_AST.Dynamic in
          let uu____4776 =
            let uu____4777 =
              let uu____4782 = resugar_term' env tm in (uu____4782, qi1) in
            FStar_Parser_AST.Quote uu____4777 in
          mk1 uu____4776
      | FStar_Syntax_Syntax.Tm_meta (e, m) ->
          let resugar_meta_desugared uu___73_4792 =
            match uu___73_4792 with
            | FStar_Syntax_Syntax.Sequence ->
                let term = resugar_term' env e in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4798, (uu____4799, (p, t11))::[], t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                      let uu____4860 =
                        let uu____4861 =
                          let uu____4870 = resugar_seq t11 in
                          (uu____4870, t2, t3) in
                        FStar_Parser_AST.Ascribed uu____4861 in
                      mk1 uu____4860
                  | uu____4873 -> t1 in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat -> resugar_term' env e
            | FStar_Syntax_Syntax.Mutable_alloc ->
                let term = resugar_term' env e in
                (match term.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Let
                     (FStar_Parser_AST.NoLetQualifier, l, t1) ->
                     mk1
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.Mutable, l, t1))
                 | uu____4919 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                let uu____4921 =
                  let uu____4922 = FStar_Syntax_Subst.compress e in
                  uu____4922.FStar_Syntax_Syntax.n in
                (match uu____4921 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____4926;
                        FStar_Syntax_Syntax.vars = uu____4927;_},
                      (term, uu____4929)::[])
                     -> resugar_term' env term
                 | uu____4958 -> failwith "mutable_rval should have app term") in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____4996 ->
                         match uu____4996 with
                         | (x, uu____5002) -> resugar_term' env x)) in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l, uu____5004, p) ->
               let uu____5006 =
                 let uu____5007 =
                   let uu____5014 = resugar_term' env e in (uu____5014, l, p) in
                 FStar_Parser_AST.Labeled uu____5007 in
               mk1 uu____5006
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1, t1) ->
               let uu____5023 =
                 let uu____5024 =
                   let uu____5033 = resugar_term' env e in
                   let uu____5034 =
                     let uu____5035 =
                       let uu____5036 =
                         let uu____5047 =
                           let uu____5054 =
                             let uu____5059 = resugar_term' env t1 in
                             (uu____5059, FStar_Parser_AST.Nothing) in
                           [uu____5054] in
                         (name1, uu____5047) in
                       FStar_Parser_AST.Construct uu____5036 in
                     mk1 uu____5035 in
                   (uu____5033, uu____5034, FStar_Pervasives_Native.None) in
                 FStar_Parser_AST.Ascribed uu____5024 in
               mk1 uu____5023
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1, uu____5077, t1) ->
               let uu____5083 =
                 let uu____5084 =
                   let uu____5093 = resugar_term' env e in
                   let uu____5094 =
                     let uu____5095 =
                       let uu____5096 =
                         let uu____5107 =
                           let uu____5114 =
                             let uu____5119 = resugar_term' env t1 in
                             (uu____5119, FStar_Parser_AST.Nothing) in
                           [uu____5114] in
                         (name1, uu____5107) in
                       FStar_Parser_AST.Construct uu____5096 in
                     mk1 uu____5095 in
                   (uu____5093, uu____5094, FStar_Pervasives_Native.None) in
                 FStar_Parser_AST.Ascribed uu____5084 in
               mk1 uu____5083)
      | FStar_Syntax_Syntax.Tm_unknown -> mk1 FStar_Parser_AST.Wild
and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env ->
    fun c ->
      let mk1 a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ, u) ->
          let t = resugar_term' env typ in
          (match u with
           | FStar_Pervasives_Native.None ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____5168 = FStar_Options.print_universes () in
               if uu____5168
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
      | FStar_Syntax_Syntax.GTotal (typ, u) ->
          let t = resugar_term' env typ in
          (match u with
           | FStar_Pervasives_Native.None ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____5229 = FStar_Options.print_universes () in
               if uu____5229
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
            let uu____5270 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ in
            (uu____5270, FStar_Parser_AST.Nothing) in
          let uu____5271 = FStar_Options.print_effect_args () in
          if uu____5271
          then
            let universe =
              FStar_List.map (fun u -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs in
            let args =
              if
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5358 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post) in
                      (uu____5358, (FStar_Pervasives_Native.snd post)) in
                    let uu____5367 =
                      let uu____5376 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre) in
                      if uu____5376 then [] else [pre] in
                    let uu____5406 =
                      let uu____5415 =
                        let uu____5424 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats) in
                        if uu____5424 then [] else [pats] in
                      FStar_List.append [post1] uu____5415 in
                    FStar_List.append uu____5367 uu____5406
                | uu____5478 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args in
            let args1 =
              FStar_List.map
                (fun uu____5507 ->
                   match uu____5507 with
                   | (e, uu____5517) ->
                       let uu____5518 = resugar_term' env e in
                       (uu____5518, FStar_Parser_AST.Nothing)) args in
            let rec aux l uu___74_5539 =
              match uu___74_5539 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5572 = resugar_term' env e in
                         (uu____5572, FStar_Parser_AST.Nothing) in
                       aux (e1 :: l) tl1
                   | uu____5577 -> aux l tl1) in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags in
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name), [result]))
and (resugar_binder' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env ->
    fun b ->
      fun r ->
        let uu____5623 = b in
        match uu____5623 with
        | (x, aq) ->
            let uu____5628 = resugar_arg_qual aq in
            FStar_Util.map_opt uu____5628
              (fun imp ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild ->
                     let uu____5642 =
                       let uu____5643 = bv_as_unique_ident x in
                       FStar_Parser_AST.Variable uu____5643 in
                     FStar_Parser_AST.mk_binder uu____5642 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5644 ->
                     let uu____5645 = FStar_Syntax_Syntax.is_null_bv x in
                     if uu____5645
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5647 =
                          let uu____5648 =
                            let uu____5653 = bv_as_unique_ident x in
                            (uu____5653, e) in
                          FStar_Parser_AST.Annotated uu____5648 in
                        FStar_Parser_AST.mk_binder uu____5647 r
                          FStar_Parser_AST.Type_level imp))
and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env ->
    fun v1 ->
      fun aqual ->
        fun body_bv ->
          fun typ_opt ->
            let mk1 a =
              let uu____5671 = FStar_Syntax_Syntax.range_of_bv v1 in
              FStar_Parser_AST.mk_pattern a uu____5671 in
            let used = FStar_Util.set_mem v1 body_bv in
            let pat =
              let uu____5674 =
                if used
                then
                  let uu____5675 =
                    let uu____5682 = bv_as_unique_ident v1 in
                    (uu____5682, aqual) in
                  FStar_Parser_AST.PatVar uu____5675
                else FStar_Parser_AST.PatWild in
              mk1 uu____5674 in
            match typ_opt with
            | FStar_Pervasives_Native.None -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown;
                  FStar_Syntax_Syntax.pos = uu____5688;
                  FStar_Syntax_Syntax.vars = uu____5689;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5699 = FStar_Options.print_bound_var_types () in
                if uu____5699
                then
                  let uu____5700 =
                    let uu____5701 =
                      let uu____5712 =
                        let uu____5719 = resugar_term' env typ in
                        (uu____5719, FStar_Pervasives_Native.None) in
                      (pat, uu____5712) in
                    FStar_Parser_AST.PatAscribed uu____5701 in
                  mk1 uu____5700
                else pat
and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.aqual ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env ->
    fun x ->
      fun qual ->
        fun body_bv ->
          let uu____5737 = resugar_arg_qual qual in
          FStar_Util.map_opt uu____5737
            (fun aqual ->
               let uu____5749 =
                 let uu____5754 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
                 FStar_All.pipe_left
                   (fun _0_39 -> FStar_Pervasives_Native.Some _0_39)
                   uu____5754 in
               resugar_bv_as_pat' env x aqual body_bv uu____5749)
and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env ->
    fun p ->
      fun branch_bv ->
        let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None) in
        let may_drop_implicits args =
          (let uu____5803 = FStar_Options.print_implicits () in
           Prims.op_Negation uu____5803) &&
            (let uu____5805 =
               FStar_List.existsML
                 (fun uu____5816 ->
                    match uu____5816 with
                    | (pattern, is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv, uu____5832)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5837 -> false
                          | uu____5838 -> true in
                        is_implicit1 && might_be_used) args in
             Prims.op_Negation uu____5805) in
        let resugar_plain_pat_cons' fv args =
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args)) in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____5891 = may_drop_implicits args in
            if uu____5891 then filter_pattern_imp args else args in
          let args2 =
            FStar_List.map
              (fun uu____5913 ->
                 match uu____5913 with
                 | (p1, b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1 in
          resugar_plain_pat_cons' fv args2
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk1 (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv, []) ->
              mk1
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv, args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____5959 =
                  let uu____5960 =
                    let uu____5961 = filter_pattern_imp args in
                    FStar_List.isEmpty uu____5961 in
                  Prims.op_Negation uu____5960 in
                if uu____5959
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk1 (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv, args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____5997 = filter_pattern_imp args in
              (match uu____5997 with
               | (hd1, false)::(tl1, false)::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false) in
                   let uu____6037 =
                     aux tl1 (FStar_Pervasives_Native.Some false) in
                   (match uu____6037 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6053 =
                       let uu____6058 =
                         let uu____6059 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args') in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6059 in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6058) in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6053);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv, args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____6104 ->
                        match uu____6104 with
                        | (p2, is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____6116 =
                                 aux p2 (FStar_Pervasives_Native.Some false) in
                               FStar_Pervasives_Native.Some uu____6116))) in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____6120;
                 FStar_Syntax_Syntax.fv_delta = uu____6121;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name, fields));_},
               args)
              ->
              let fields1 =
                let uu____6148 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f -> FStar_Ident.lid_of_ids [f])) in
                FStar_All.pipe_right uu____6148 FStar_List.rev in
              let args1 =
                let uu____6164 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____6184 ->
                          match uu____6184 with
                          | (p2, b) ->
                              aux p2 (FStar_Pervasives_Native.Some b))) in
                FStar_All.pipe_right uu____6164 FStar_List.rev in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([], []) -> []
                | ([], hd1::tl1) -> []
                | (hd1::tl1, []) ->
                    let uu____6254 = map21 tl1 [] in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6254
                | (hd1::tl1, hd2::tl2) ->
                    let uu____6277 = map21 tl1 tl2 in (hd1, hd2) ::
                      uu____6277 in
              let args2 =
                let uu____6295 = map21 fields1 args1 in
                FStar_All.pipe_right uu____6295 FStar_List.rev in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv, args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6337 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
              (match uu____6337 with
               | FStar_Pervasives_Native.Some (op, uu____6347) ->
                   mk1
                     (FStar_Parser_AST.PatOp
                        (FStar_Ident.mk_ident
                           (op,
                             ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
               | FStar_Pervasives_Native.None ->
                   let uu____6364 = to_arg_qual imp_opt in
                   resugar_bv_as_pat' env v1 uu____6364 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6369 ->
              mk1 FStar_Parser_AST.PatWild
          | FStar_Syntax_Syntax.Pat_dot_term (bv, term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term) in
        aux p FStar_Pervasives_Native.None
let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___75_6382 ->
    match uu___75_6382 with
    | FStar_Syntax_Syntax.Assumption ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Visible
    | FStar_Syntax_Syntax.Irreducible ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Reifiable ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____6388 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6389 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6390 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6395 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6404 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6413 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName -> FStar_Pervasives_Native.None
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___76_6416 ->
    match uu___76_6416 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff -> FStar_Parser_AST.LightOff
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts, FStar_Parser_AST.tycon)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun datacon_ses ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid, uvs, bs, t, uu____6446, datacons) ->
            let uu____6456 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1 ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6483, uu____6484, uu____6485, inductive_lid,
                           uu____6487, uu____6488)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6493 -> failwith "unexpected")) in
            (match uu____6456 with
             | (current_datacons, other_datacons) ->
                 let bs1 =
                   let uu____6518 = FStar_Options.print_implicits () in
                   if uu____6518 then bs else filter_imp bs in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos)) in
                 let tyc =
                   let uu____6528 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___77_6533 ->
                             match uu___77_6533 with
                             | FStar_Syntax_Syntax.RecordType uu____6534 ->
                                 true
                             | uu____6543 -> false)) in
                   if uu____6528
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6591, univs1, term, uu____6594, num,
                            uu____6596)
                           ->
                           let uu____6601 =
                             let uu____6602 =
                               FStar_Syntax_Subst.compress term in
                             uu____6602.FStar_Syntax_Syntax.n in
                           (match uu____6601 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3, uu____6616)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6677 ->
                                          match uu____6677 with
                                          | (b, qual) ->
                                              let uu____6692 =
                                                let uu____6693 =
                                                  bv_as_unique_ident b in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6693 in
                                              let uu____6694 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort in
                                              (uu____6692, uu____6694,
                                                FStar_Pervasives_Native.None))) in
                                FStar_List.append mfields fields
                            | uu____6705 -> failwith "unexpected")
                       | uu____6716 -> failwith "unexpected" in
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
                            (l, univs1, term, uu____6837, num, uu____6839) ->
                            let c =
                              let uu____6857 =
                                let uu____6860 = resugar_term' env term in
                                FStar_Pervasives_Native.Some uu____6860 in
                              ((l.FStar_Ident.ident), uu____6857,
                                FStar_Pervasives_Native.None, false) in
                            c :: constructors
                        | uu____6877 -> failwith "unexpected" in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors)) in
                 (other_datacons, tyc))
        | uu____6953 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r ->
    fun q ->
      fun d' ->
        let uu____6971 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6971;
          FStar_Parser_AST.attrs = []
        }
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se ->
    fun d' ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env ->
    fun name ->
      fun ts ->
        let uu____6987 = ts in
        match uu____6987 with
        | (univs1, typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
            let uu____6995 =
              let uu____6996 =
                let uu____7009 =
                  let uu____7018 =
                    let uu____7025 =
                      let uu____7026 =
                        let uu____7039 = resugar_term' env typ in
                        (name1, [], FStar_Pervasives_Native.None, uu____7039) in
                      FStar_Parser_AST.TyconAbbrev uu____7026 in
                    (uu____7025, FStar_Pervasives_Native.None) in
                  [uu____7018] in
                (false, uu____7009) in
              FStar_Parser_AST.Tycon uu____6996 in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6995
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env -> fun ts -> resugar_tscheme'' env "tsheme" ts
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env ->
    fun for_free ->
      fun r ->
        fun q ->
          fun ed ->
            let resugar_action d for_free1 =
              let action_params =
                FStar_Syntax_Subst.open_binders
                  d.FStar_Syntax_Syntax.action_params in
              let uu____7099 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn in
              match uu____7099 with
              | (bs, action_defn) ->
                  let uu____7106 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ in
                  (match uu____7106 with
                   | (bs1, action_typ) ->
                       let action_params1 =
                         let uu____7114 = FStar_Options.print_implicits () in
                         if uu____7114
                         then action_params
                         else filter_imp action_params in
                       let action_params2 =
                         let uu____7119 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ()) (fun b -> resugar_binder' env b r)) in
                         FStar_All.pipe_right uu____7119 FStar_List.rev in
                       let action_defn1 = resugar_term' env action_defn in
                       let action_typ1 = resugar_term' env action_typ in
                       if for_free1
                       then
                         let a =
                           let uu____7133 =
                             let uu____7144 =
                               FStar_Ident.lid_of_str "construct" in
                             (uu____7144,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)]) in
                           FStar_Parser_AST.Construct uu____7133 in
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
            let uu____7218 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature in
            match uu____7218 with
            | (eff_binders, eff_typ) ->
                let eff_binders1 =
                  let uu____7226 = FStar_Options.print_implicits () in
                  if uu____7226 then eff_binders else filter_imp eff_binders in
                let eff_binders2 =
                  let uu____7231 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b -> resugar_binder' env b r)) in
                  FStar_All.pipe_right uu____7231 FStar_List.rev in
                let eff_typ1 = resugar_term' env eff_typ in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.ret_wp in
                let if_then_else1 =
                  resugar_tscheme'' env "if_then_else"
                    ed.FStar_Syntax_Syntax.if_then_else in
                let ite_wp =
                  resugar_tscheme'' env "ite_wp"
                    ed.FStar_Syntax_Syntax.ite_wp in
                let stronger =
                  resugar_tscheme'' env "stronger"
                    ed.FStar_Syntax_Syntax.stronger in
                let close_wp =
                  resugar_tscheme'' env "close_wp"
                    ed.FStar_Syntax_Syntax.close_wp in
                let assert_p =
                  resugar_tscheme'' env "assert_p"
                    ed.FStar_Syntax_Syntax.assert_p in
                let assume_p =
                  resugar_tscheme'' env "assume_p"
                    ed.FStar_Syntax_Syntax.assume_p in
                let null_wp =
                  resugar_tscheme'' env "null_wp"
                    ed.FStar_Syntax_Syntax.null_wp in
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial in
                let repr =
                  resugar_tscheme'' env "repr"
                    ([], (ed.FStar_Syntax_Syntax.repr)) in
                let return_repr =
                  resugar_tscheme'' env "return_repr"
                    ed.FStar_Syntax_Syntax.return_repr in
                let bind_repr =
                  resugar_tscheme'' env "bind_repr"
                    ed.FStar_Syntax_Syntax.bind_repr in
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
                    (FStar_List.map (fun a -> resugar_action a false)) in
                let decls = FStar_List.append mandatory_members_decls actions in
                mk_decl r q
                  (FStar_Parser_AST.NewEffect
                     (FStar_Parser_AST.DefineEffect
                        (eff_name, eff_binders2, eff_typ1, decls)))
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____7291) ->
          let uu____7300 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1 ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7322 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7339 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7346 -> false
                    | uu____7361 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
          (match uu____7300 with
           | (decl_typ_ses, datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7393 se1 =
                 match uu____7393 with
                 | (datacon_ses1, tycons) ->
                     let uu____7419 = resugar_typ env datacon_ses1 se1 in
                     (match uu____7419 with
                      | (datacon_ses2, tyc) ->
                          (datacon_ses2, (tyc :: tycons))) in
               let uu____7434 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses in
               (match uu____7434 with
                | (leftover_datacons, tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7469 =
                           let uu____7470 =
                             let uu____7471 =
                               let uu____7484 =
                                 FStar_List.map
                                   (fun tyc ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons in
                               (false, uu____7484) in
                             FStar_Parser_AST.Tycon uu____7471 in
                           decl'_to_decl se uu____7470 in
                         FStar_Pervasives_Native.Some uu____7469
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l, uu____7515, uu____7516, uu____7517,
                               uu____7518, uu____7519)
                              ->
                              let uu____7524 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None)) in
                              FStar_Pervasives_Native.Some uu____7524
                          | uu____7527 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7530 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____7536) ->
          let uu____7541 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___78_7547 ->
                    match uu___78_7547 with
                    | FStar_Syntax_Syntax.Projector (uu____7548, uu____7549)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7550 -> true
                    | uu____7551 -> false)) in
          if uu____7541
          then FStar_Pervasives_Native.None
          else
            (let mk1 e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng in
             let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
             let desugared_let =
               mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
             let t = resugar_term' env desugared_let in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec, lets, uu____7574) ->
                 let uu____7603 =
                   let uu____7604 =
                     let uu____7605 =
                       let uu____7616 =
                         FStar_List.map FStar_Pervasives_Native.snd lets in
                       (isrec, uu____7616) in
                     FStar_Parser_AST.TopLevelLet uu____7605 in
                   decl'_to_decl se uu____7604 in
                 FStar_Pervasives_Native.Some uu____7603
             | uu____7653 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid, uu____7657, fml) ->
          let uu____7659 =
            let uu____7660 =
              let uu____7661 =
                let uu____7666 = resugar_term' env fml in
                ((lid.FStar_Ident.ident), uu____7666) in
              FStar_Parser_AST.Assume uu____7661 in
            decl'_to_decl se uu____7660 in
          FStar_Pervasives_Native.Some uu____7659
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7668 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed in
          FStar_Pervasives_Native.Some uu____7668
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7670 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed in
          FStar_Pervasives_Native.Some uu____7670
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source in
          let dst = e.FStar_Syntax_Syntax.target in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7679, t) ->
                let uu____7691 = resugar_term' env t in
                FStar_Pervasives_Native.Some uu____7691
            | uu____7692 -> FStar_Pervasives_Native.None in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7700, t) ->
                let uu____7712 = resugar_term' env t in
                FStar_Pervasives_Native.Some uu____7712
            | uu____7713 -> FStar_Pervasives_Native.None in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t, FStar_Pervasives_Native.None)
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp, FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7737 -> failwith "Should not happen hopefully" in
          let uu____7746 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 }) in
          FStar_Pervasives_Native.Some uu____7746
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags1) ->
          let uu____7756 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____7756 with
           | (bs1, c1) ->
               let bs2 =
                 let uu____7766 = FStar_Options.print_implicits () in
                 if uu____7766 then bs1 else filter_imp bs1 in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng)) in
               let uu____7775 =
                 let uu____7776 =
                   let uu____7777 =
                     let uu____7790 =
                       let uu____7799 =
                         let uu____7806 =
                           let uu____7807 =
                             let uu____7820 = resugar_comp' env c1 in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____7820) in
                           FStar_Parser_AST.TyconAbbrev uu____7807 in
                         (uu____7806, FStar_Pervasives_Native.None) in
                       [uu____7799] in
                     (false, uu____7790) in
                   FStar_Parser_AST.Tycon uu____7777 in
                 decl'_to_decl se uu____7776 in
               FStar_Pervasives_Native.Some uu____7775)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____7848 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
          FStar_Pervasives_Native.Some uu____7848
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
          let uu____7852 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___79_7858 ->
                    match uu___79_7858 with
                    | FStar_Syntax_Syntax.Projector (uu____7859, uu____7860)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7861 -> true
                    | uu____7862 -> false)) in
          if uu____7852
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____7867 =
                 (let uu____7870 = FStar_Options.print_universes () in
                  Prims.op_Negation uu____7870) || (FStar_List.isEmpty uvs) in
               if uu____7867
               then resugar_term' env t
               else
                 (let uu____7872 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____7872 with
                  | (uvs1, t1) ->
                      let universes = universe_to_string uvs1 in
                      let uu____7880 = resugar_term' env t1 in
                      label universes uu____7880) in
             let uu____7881 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
             FStar_Pervasives_Native.Some uu____7881)
      | FStar_Syntax_Syntax.Sig_splice t ->
          let uu____7883 =
            let uu____7884 =
              let uu____7885 = resugar_term' env t in
              FStar_Parser_AST.Splice uu____7885 in
            decl'_to_decl se uu____7884 in
          FStar_Pervasives_Native.Some uu____7883
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7886 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____7903 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____7918 ->
          FStar_Pervasives_Native.None
let (empty_env : FStar_Syntax_DsEnv.env) = FStar_Syntax_DsEnv.empty_env ()
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f -> f empty_env
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t -> let uu____7934 = noenv resugar_term' in uu____7934 t
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se -> let uu____7946 = noenv resugar_sigelt' in uu____7946 se
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c -> let uu____7958 = noenv resugar_comp' in uu____7958 c
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p ->
    fun branch_bv ->
      let uu____7973 = noenv resugar_pat' in uu____7973 p branch_bv
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b -> fun r -> let uu____7996 = noenv resugar_binder' in uu____7996 b r
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts -> let uu____8012 = noenv resugar_tscheme' in uu____8012 ts
let (resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun for_free ->
    fun r ->
      fun q ->
        fun ed ->
          let uu____8033 = noenv resugar_eff_decl' in
          uu____8033 for_free r q ed