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
         (fun uu___182_127  ->
            match uu___182_127 with
            | (uu____134,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____135)) -> false
            | uu____138 -> true))
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
      | uu____204 -> (n1, u)
let universe_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____213 = FStar_Options.print_universes () in
    if uu____213
    then
      let uu____214 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1 in
      FStar_All.pipe_right uu____214 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____247 ->
          let uu____248 = universe_to_int (Prims.parse_int "0") u in
          (match uu____248 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____255 =
                      let uu____256 =
                        let uu____257 =
                          let uu____268 = FStar_Util.string_of_int n1 in
                          (uu____268, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____257 in
                      FStar_Parser_AST.Const uu____256 in
                    mk1 uu____255 r
                | uu____279 ->
                    let e1 =
                      let uu____281 =
                        let uu____282 =
                          let uu____283 =
                            let uu____294 = FStar_Util.string_of_int n1 in
                            (uu____294, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____283 in
                        FStar_Parser_AST.Const uu____282 in
                      mk1 uu____281 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____311 ->
               let t =
                 let uu____315 =
                   let uu____316 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____316 in
                 mk1 uu____315 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____322 =
                        let uu____323 =
                          let uu____330 = resugar_universe x r in
                          (acc, uu____330, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____323 in
                      mk1 uu____322 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____332 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____343 =
              let uu____348 =
                let uu____349 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____349 in
              (uu____348, r) in
            FStar_Ident.mk_ident uu____343 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op:
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___183_369 =
      match uu___183_369 with
      | "Amp" -> FStar_Pervasives_Native.Some ("&", (Prims.parse_int "0"))
      | "At" -> FStar_Pervasives_Native.Some ("@", (Prims.parse_int "0"))
      | "Plus" -> FStar_Pervasives_Native.Some ("+", (Prims.parse_int "0"))
      | "Minus" -> FStar_Pervasives_Native.Some ("-", (Prims.parse_int "0"))
      | "Subtraction" ->
          FStar_Pervasives_Native.Some ("-", (Prims.parse_int "2"))
      | "Slash" -> FStar_Pervasives_Native.Some ("/", (Prims.parse_int "0"))
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
      | uu____444 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____471 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____481 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____481 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____489 ->
               let op =
                 let uu____493 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____527) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____493 in
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
      let uu____714 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____714 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____762 ->
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
                (let uu____815 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____815
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____831 =
      let uu____832 = FStar_Syntax_Subst.compress t in
      uu____832.FStar_Syntax_Syntax.n in
    match uu____831 with
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
        let uu____855 = string_to_op s in
        (match uu____855 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____881 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____894 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____903 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____908 -> true
    | uu____909 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____940 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____940 in
    let var a r =
      let uu____948 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____948 in
    let uu____949 =
      let uu____950 = FStar_Syntax_Subst.compress t in
      uu____950.FStar_Syntax_Syntax.n in
    match uu____949 with
    | FStar_Syntax_Syntax.Tm_delayed uu____953 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____980 = let uu____983 = bv_as_unique_ident x in [uu____983] in
          FStar_Ident.lid_of_ids uu____980 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____986 = let uu____989 = bv_as_unique_ident x in [uu____989] in
          FStar_Ident.lid_of_ids uu____986 in
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
          let uu____1007 =
            let uu____1008 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____1008 in
          mk1 uu____1007
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
             | uu____1018 -> failwith "wrong projector format")
          else
            (let uu____1022 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1025 =
                    let uu____1026 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1026 in
                  let uu____1027 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1025 <> uu____1027) in
             if uu____1022
             then
               let uu____1028 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1028
             else
               (let uu____1030 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1030))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1037 = FStar_Options.print_universes () in
        if uu____1037
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1044 =
                   let uu____1045 =
                     let uu____1052 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1052, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1045 in
                 mk1 uu____1044) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1055 = FStar_Syntax_Syntax.is_teff t in
        if uu____1055
        then
          let uu____1056 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1056
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1059 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1059
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1060 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1060
         | uu____1061 ->
             let uu____1062 = FStar_Options.print_universes () in
             if uu____1062
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1080 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1080))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1083) ->
        let uu____1104 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1104 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1112 = FStar_Options.print_implicits () in
               if uu____1112 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1126  ->
                       match uu____1126 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1156 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1156 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1164 = FStar_Options.print_implicits () in
               if uu____1164 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1170 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1170 FStar_List.rev in
             let rec aux body3 uu___184_1189 =
               match uu___184_1189 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1205 =
          let uu____1210 =
            let uu____1211 = FStar_Syntax_Syntax.mk_binder x in [uu____1211] in
          FStar_Syntax_Subst.open_term uu____1210 phi in
        (match uu____1205 with
         | (x1,phi1) ->
             let b =
               let uu____1215 =
                 let uu____1218 = FStar_List.hd x1 in
                 resugar_binder uu____1218 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1215 in
             let uu____1223 =
               let uu____1224 =
                 let uu____1229 = resugar_term phi1 in (b, uu____1229) in
               FStar_Parser_AST.Refine uu____1224 in
             mk1 uu____1223)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___185_1271 =
          match uu___185_1271 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1341 -> failwith "last of an empty list" in
        let rec last_two uu___186_1377 =
          match uu___186_1377 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1408::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1485::t1 -> last_two t1 in
        let rec last_three uu___187_1526 =
          match uu___187_1526 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1557::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1584::uu____1585::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1693::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1779  ->
                    match uu____1779 with
                    | (e2,qual) ->
                        let uu____1798 = resugar_term e2 in
                        (uu____1798, qual))) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1814  ->
                 match uu____1814 with
                 | (x,qual) ->
                     let uu____1827 =
                       let uu____1828 =
                         let uu____1835 = resugar_imp qual in
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
                           (map_opt
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
                            (map_opt
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
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____2930 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2930 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
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
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
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
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
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
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
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
                                        (map_opt
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
                 fun a357  ->
                   (Obj.magic
                      (if uu____3872
                       then FStar_Pervasives_Native.fst
                       else
                         (fun uu___188_3893  ->
                            match uu___188_3893 with
                            | ((pat,body2),univs1) ->
                                let uu____3913 =
                                  if univs1 = ""
                                  then body2
                                  else
                                    mk1
                                      (FStar_Parser_AST.Labeled
                                         (body2, univs1, true)) in
                                (pat, uu____3913)))) a357 in
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
          Prims.strcat "uu___unification_ " uu____3962 in
        let uu____3964 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____3964
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___189_3974 =
          match uu___189_3974 with
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
                      let uu____4201 =
                        let uu____4202 =
                          let uu____4203 = resugar_term h in
                          parser_term_to_string uu____4203 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4202 in
                      FStar_Errors.Err uu____4201 in
                    raise uu____4200 in
              let uu____4220 =
                try
                  let uu____4272 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4272
                with
                | FStar_Errors.Err uu____4293 ->
                    let uu____4294 =
                      let uu____4295 =
                        let uu____4300 =
                          let uu____4301 =
                            let uu____4302 = resugar_term e in
                            parser_term_to_string uu____4302 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4301 in
                        (uu____4300, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4295 in
                    raise uu____4294 in
              (match uu____4220 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4356 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4356, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.map
                       (fun uu____4379  ->
                          match uu____4379 with
                          | (t1,q) ->
                              let uu____4396 = resugar_term t1 in
                              let uu____4397 = resugar_imp q in
                              (uu____4396, uu____4397)) args in
                   let args2 =
                     let uu____4405 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4407 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4407) in
                     if uu____4405
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4430,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4455 =
                      let uu____4456 =
                        let uu____4465 = resugar_seq t11 in
                        (uu____4465, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4456 in
                    mk1 uu____4455
                | uu____4468 -> t1 in
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
               | uu____4490 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4492 =
                let uu____4493 = FStar_Syntax_Subst.compress e in
                uu____4493.FStar_Syntax_Syntax.n in
              (match uu____4492 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4497;
                      FStar_Syntax_Syntax.vars = uu____4498;_},(term,uu____4500)::[])
                   -> resugar_term term
               | uu____4529 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4567  ->
                       match uu____4567 with
                       | (x,uu____4573) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4575,p) ->
             let uu____4577 =
               let uu____4578 =
                 let uu____4585 = resugar_term e in (uu____4585, l, p) in
               FStar_Parser_AST.Labeled uu____4578 in
             mk1 uu____4577
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4587,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4596 =
               let uu____4597 =
                 let uu____4606 = resugar_term e in
                 let uu____4607 =
                   let uu____4608 =
                     let uu____4609 =
                       let uu____4620 =
                         let uu____4627 =
                           let uu____4632 = resugar_term t1 in
                           (uu____4632, FStar_Parser_AST.Nothing) in
                         [uu____4627] in
                       (name1, uu____4620) in
                     FStar_Parser_AST.Construct uu____4609 in
                   mk1 uu____4608 in
                 (uu____4606, uu____4607, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4597 in
             mk1 uu____4596
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4650,t1) ->
             let uu____4656 =
               let uu____4657 =
                 let uu____4666 = resugar_term e in
                 let uu____4667 =
                   let uu____4668 =
                     let uu____4669 =
                       let uu____4680 =
                         let uu____4687 =
                           let uu____4692 = resugar_term t1 in
                           (uu____4692, FStar_Parser_AST.Nothing) in
                         [uu____4687] in
                       (name1, uu____4680) in
                     FStar_Parser_AST.Construct uu____4669 in
                   mk1 uu____4668 in
                 (uu____4666, uu____4667, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4657 in
             mk1 uu____4656)
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
             let uu____4740 = FStar_Options.print_universes () in
             if uu____4740
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
             let uu____4801 = FStar_Options.print_universes () in
             if uu____4801
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
          let uu____4842 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4842, FStar_Parser_AST.Nothing) in
        let uu____4843 = FStar_Options.print_effect_args () in
        if uu____4843
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___190_4900 =
                match uu___190_4900 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____4961 -> aux l tl1
                     | uu____4968 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5003  ->
                 match uu____5003 with
                 | (e,uu____5013) ->
                     let uu____5014 = resugar_term e in
                     (uu____5014, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___191_5035 =
            match uu___191_5035 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5068 = resugar_term e in
                       (uu____5068, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5073 -> aux l tl1) in
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
      let uu____5118 = b in
      match uu____5118 with
      | (x,aq) ->
          let uu____5123 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5123
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5137 =
                     let uu____5138 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5138 in
                   FStar_Parser_AST.mk_binder uu____5137 r
                     FStar_Parser_AST.Type_level imp
               | uu____5139 ->
                   let uu____5140 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5140
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5142 =
                        let uu____5143 =
                          let uu____5148 = bv_as_unique_ident x in
                          (uu____5148, e) in
                        FStar_Parser_AST.Annotated uu____5143 in
                      FStar_Parser_AST.mk_binder uu____5142 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5157 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5157 in
      let uu____5158 =
        let uu____5159 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5159.FStar_Syntax_Syntax.n in
      match uu____5158 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5167 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5167
          else
            (let uu____5169 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5169
               (fun aq  ->
                  let uu____5181 =
                    let uu____5182 =
                      let uu____5183 =
                        let uu____5190 = bv_as_unique_ident x in
                        (uu____5190, aq) in
                      FStar_Parser_AST.PatVar uu____5183 in
                    mk1 uu____5182 in
                  FStar_Pervasives_Native.Some uu____5181))
      | uu____5193 ->
          let uu____5194 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5194
            (fun aq  ->
               let pat =
                 let uu____5209 =
                   let uu____5210 =
                     let uu____5217 = bv_as_unique_ident x in
                     (uu____5217, aq) in
                   FStar_Parser_AST.PatVar uu____5210 in
                 mk1 uu____5209 in
               let uu____5220 = FStar_Options.print_bound_var_types () in
               if uu____5220
               then
                 let uu____5223 =
                   let uu____5224 =
                     let uu____5225 =
                       let uu____5230 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5230) in
                     FStar_Parser_AST.PatAscribed uu____5225 in
                   mk1 uu____5224 in
                 FStar_Pervasives_Native.Some uu____5223
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
              (fun uu____5307  ->
                 match uu____5307 with
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
              (fun uu____5342  ->
                 match uu____5342 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5349 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5349
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5355;
             FStar_Syntax_Syntax.fv_delta = uu____5356;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5383 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5383 FStar_List.rev in
          let args1 =
            let uu____5399 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5419  ->
                      match uu____5419 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5399 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5489 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5489
            | (hd1::tl1,hd2::tl2) ->
                let uu____5512 = map21 tl1 tl2 in (hd1, hd2) :: uu____5512 in
          let args2 =
            let uu____5530 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5530 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5581  ->
                 match uu____5581 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5591 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5591 with
           | FStar_Pervasives_Native.Some (op,uu____5599) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5608 =
                 let uu____5609 =
                   let uu____5616 = bv_as_unique_ident v1 in
                   let uu____5617 = to_arg_qual imp_opt in
                   (uu____5616, uu____5617) in
                 FStar_Parser_AST.PatVar uu____5609 in
               mk1 uu____5608)
      | FStar_Syntax_Syntax.Pat_wild uu____5622 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5630 =
              let uu____5631 =
                let uu____5638 = bv_as_unique_ident bv in
                (uu____5638,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5631 in
            mk1 uu____5630 in
          let uu____5641 = FStar_Options.print_bound_var_types () in
          if uu____5641
          then
            let uu____5642 =
              let uu____5643 =
                let uu____5648 = resugar_term term in (pat, uu____5648) in
              FStar_Parser_AST.PatAscribed uu____5643 in
            mk1 uu____5642
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___192_5655  ->
    match uu___192_5655 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5664 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5665 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5666 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5671 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5680 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5689 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___193_5693  ->
    match uu___193_5693 with
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
          (tylid,uvs,bs,t,uu____5722,datacons) ->
          let uu____5732 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5759,uu____5760,uu____5761,inductive_lid,uu____5763,uu____5764)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5769 -> failwith "unexpected")) in
          (match uu____5732 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5788 = FStar_Options.print_implicits () in
                 if uu____5788 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5798 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___194_5803  ->
                           match uu___194_5803 with
                           | FStar_Syntax_Syntax.RecordType uu____5804 ->
                               true
                           | uu____5813 -> false)) in
                 if uu____5798
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5861,univs1,term,uu____5864,num,uu____5866)
                         ->
                         let uu____5871 =
                           let uu____5872 = FStar_Syntax_Subst.compress term in
                           uu____5872.FStar_Syntax_Syntax.n in
                         (match uu____5871 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5886) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____5947  ->
                                        match uu____5947 with
                                        | (b,qual) ->
                                            let uu____5962 =
                                              let uu____5963 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____5963 in
                                            let uu____5964 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____5962, uu____5964,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____5975 -> failwith "unexpected")
                     | uu____5986 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6107,num,uu____6109) ->
                          let c =
                            let uu____6127 =
                              let uu____6130 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6130 in
                            ((l.FStar_Ident.ident), uu____6127,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6147 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6223 ->
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
        let uu____6244 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6244;
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
      let uu____6261 = ts in
      match uu____6261 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6269 =
            let uu____6270 =
              let uu____6283 =
                let uu____6292 =
                  let uu____6299 =
                    let uu____6300 =
                      let uu____6313 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6313) in
                    FStar_Parser_AST.TyconAbbrev uu____6300 in
                  (uu____6299, FStar_Pervasives_Native.None) in
                [uu____6292] in
              (false, uu____6283) in
            FStar_Parser_AST.Tycon uu____6270 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6269
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
            let uu____6372 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6372 with
            | (bs,action_defn) ->
                let uu____6379 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6379 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6387 = FStar_Options.print_implicits () in
                       if uu____6387
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6392 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6392 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6406 =
                           let uu____6417 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6417,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6406 in
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
          let uu____6491 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6491 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6499 = FStar_Options.print_implicits () in
                if uu____6499 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6504 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6504 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6562) ->
        let uu____6571 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6593 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6610 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6617 -> false
                  | uu____6632 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6571 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6664 se1 =
               match uu____6664 with
               | (datacon_ses1,tycons) ->
                   let uu____6690 = resugar_typ datacon_ses1 se1 in
                   (match uu____6690 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6705 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6705 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6740 =
                         let uu____6741 =
                           let uu____6742 =
                             let uu____6755 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6755) in
                           FStar_Parser_AST.Tycon uu____6742 in
                         decl'_to_decl se uu____6741 in
                       FStar_Pervasives_Native.Some uu____6740
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6786,uu____6787,uu____6788,uu____6789,uu____6790)
                            ->
                            let uu____6795 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6795
                        | uu____6798 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6801 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6807) ->
        let uu____6812 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___195_6818  ->
                  match uu___195_6818 with
                  | FStar_Syntax_Syntax.Projector (uu____6819,uu____6820) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6821 -> true
                  | uu____6822 -> false)) in
        if uu____6812
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6845) ->
               let uu____6858 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6858
           | uu____6865 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6869,fml) ->
        let uu____6871 =
          let uu____6872 =
            let uu____6873 =
              let uu____6878 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6878) in
            FStar_Parser_AST.Assume uu____6873 in
          decl'_to_decl se uu____6872 in
        FStar_Pervasives_Native.Some uu____6871
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6880 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6880
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6882 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6882
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6891,t) ->
              let uu____6903 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6903
          | uu____6904 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____6912,t) ->
              let uu____6924 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6924
          | uu____6925 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____6949 -> failwith "Should not happen hopefully" in
        let uu____6958 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____6958
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____6968 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____6968 with
         | (bs1,c1) ->
             let bs2 =
               let uu____6978 = FStar_Options.print_implicits () in
               if uu____6978 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____6987 =
               let uu____6988 =
                 let uu____6989 =
                   let uu____7002 =
                     let uu____7011 =
                       let uu____7018 =
                         let uu____7019 =
                           let uu____7032 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7032) in
                         FStar_Parser_AST.TyconAbbrev uu____7019 in
                       (uu____7018, FStar_Pervasives_Native.None) in
                     [uu____7011] in
                   (false, uu____7002) in
                 FStar_Parser_AST.Tycon uu____6989 in
               decl'_to_decl se uu____6988 in
             FStar_Pervasives_Native.Some uu____6987)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7060 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7060
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7064 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_7070  ->
                  match uu___196_7070 with
                  | FStar_Syntax_Syntax.Projector (uu____7071,uu____7072) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7073 -> true
                  | uu____7074 -> false)) in
        if uu____7064
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7079 =
               (let uu____7082 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7082) || (FStar_List.isEmpty uvs) in
             if uu____7079
             then resugar_term t
             else
               (let uu____7084 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7084 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7092 =
                      let uu____7093 =
                        let uu____7100 = resugar_term t1 in
                        (uu____7100, universes, true) in
                      FStar_Parser_AST.Labeled uu____7093 in
                    FStar_Parser_AST.mk_term uu____7092
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____7101 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7101)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7102 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7119 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7134 -> FStar_Pervasives_Native.None