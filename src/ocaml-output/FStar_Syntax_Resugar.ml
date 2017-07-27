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
      | uu____452 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____479 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____489 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____489 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____497 ->
               let op =
                 let uu____501 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____535) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____501 in
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
      let uu____722 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____722 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____770 ->
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
                (let uu____823 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____823
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None) in
    let uu____839 =
      let uu____840 = FStar_Syntax_Subst.compress t in
      uu____840.FStar_Syntax_Syntax.n in
    match uu____839 with
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
        let uu____863 = string_to_op s in
        (match uu____863 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____889 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____902 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____911 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____916 -> true
    | uu____917 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____948 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____948 in
    let var a r =
      let uu____956 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____956 in
    let uu____957 =
      let uu____958 = FStar_Syntax_Subst.compress t in
      uu____958.FStar_Syntax_Syntax.n in
    match uu____957 with
    | FStar_Syntax_Syntax.Tm_delayed uu____961 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____988 = let uu____991 = bv_as_unique_ident x in [uu____991] in
          FStar_Ident.lid_of_ids uu____988 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____994 = let uu____997 = bv_as_unique_ident x in [uu____997] in
          FStar_Ident.lid_of_ids uu____994 in
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
          let uu____1015 =
            let uu____1016 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____1016 in
          mk1 uu____1015
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
             | uu____1026 -> failwith "wrong projector format")
          else
            (let uu____1030 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1033 =
                    let uu____1034 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1034 in
                  let uu____1035 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1033 <> uu____1035) in
             if uu____1030
             then
               let uu____1036 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1036
             else
               (let uu____1038 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1038))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1045 = FStar_Options.print_universes () in
        if uu____1045
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1052 =
                   let uu____1053 =
                     let uu____1060 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1060, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1053 in
                 mk1 uu____1052) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1063 = FStar_Syntax_Syntax.is_teff t in
        if uu____1063
        then
          let uu____1064 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1064
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1067 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1067
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1068 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1068
         | uu____1069 ->
             let uu____1070 = FStar_Options.print_universes () in
             if uu____1070
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1088 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1088))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1091) ->
        let uu____1112 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1112 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1120 = FStar_Options.print_implicits () in
               if uu____1120 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1134  ->
                       match uu____1134 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1164 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1164 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1172 = FStar_Options.print_implicits () in
               if uu____1172 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1178 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1178 FStar_List.rev in
             let rec aux body3 uu___184_1197 =
               match uu___184_1197 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1213 =
          let uu____1218 =
            let uu____1219 = FStar_Syntax_Syntax.mk_binder x in [uu____1219] in
          FStar_Syntax_Subst.open_term uu____1218 phi in
        (match uu____1213 with
         | (x1,phi1) ->
             let b =
               let uu____1223 =
                 let uu____1226 = FStar_List.hd x1 in
                 resugar_binder uu____1226 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1223 in
             let uu____1231 =
               let uu____1232 =
                 let uu____1237 = resugar_term phi1 in (b, uu____1237) in
               FStar_Parser_AST.Refine uu____1232 in
             mk1 uu____1231)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___185_1279 =
          match uu___185_1279 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1349 -> failwith "last of an empty list" in
        let rec last_two uu___186_1385 =
          match uu___186_1385 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1416::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1493::t1 -> last_two t1 in
        let rec last_three uu___187_1534 =
          match uu___187_1534 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1565::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1592::uu____1593::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1701::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1787  ->
                    match uu____1787 with
                    | (e2,qual) ->
                        let uu____1806 = resugar_term e2 in
                        (uu____1806, qual))) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1822  ->
                 match uu____1822 with
                 | (x,qual) ->
                     let uu____1835 =
                       let uu____1836 =
                         let uu____1843 = resugar_imp qual in
                         (acc, x, uu____1843) in
                       FStar_Parser_AST.App uu____1836 in
                     mk1 uu____1835) e2 args2 in
        let args1 =
          let uu____1853 = FStar_Options.print_implicits () in
          if uu____1853 then args else filter_imp args in
        let uu____1865 = resugar_term_as_op e in
        (match uu____1865 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1876) ->
             (match args1 with
              | (fst1,uu____1882)::(snd1,uu____1884)::rest ->
                  let e1 =
                    let uu____1915 =
                      let uu____1916 =
                        let uu____1923 =
                          let uu____1926 = resugar_term fst1 in
                          let uu____1927 =
                            let uu____1930 = resugar_term snd1 in
                            [uu____1930] in
                          uu____1926 :: uu____1927 in
                        ((FStar_Ident.id_of_text "*"), uu____1923) in
                      FStar_Parser_AST.Op uu____1916 in
                    mk1 uu____1915 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1943  ->
                         match uu____1943 with
                         | (x,uu____1949) ->
                             let uu____1950 =
                               let uu____1951 =
                                 let uu____1958 =
                                   let uu____1961 =
                                     let uu____1964 = resugar_term x in
                                     [uu____1964] in
                                   e1 :: uu____1961 in
                                 ((FStar_Ident.id_of_text "*"), uu____1958) in
                               FStar_Parser_AST.Op uu____1951 in
                             mk1 uu____1950) e1 rest
              | uu____1967 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1976) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2002)::[] -> b
               | uu____2019 -> failwith "wrong arguments to dtuple" in
             let uu____2030 =
               let uu____2031 = FStar_Syntax_Subst.compress body in
               uu____2031.FStar_Syntax_Syntax.n in
             (match uu____2030 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2036) ->
                  let uu____2057 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2057 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2065 = FStar_Options.print_implicits () in
                         if uu____2065 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2077 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2098  ->
                            match uu____2098 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2110) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2116) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2121 = FStar_List.hd args1 in
             (match uu____2121 with
              | (t1,uu____2135) ->
                  let uu____2140 =
                    let uu____2141 = FStar_Syntax_Subst.compress t1 in
                    uu____2141.FStar_Syntax_Syntax.n in
                  (match uu____2140 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2146 =
                         let uu____2147 =
                           let uu____2152 = resugar_term t1 in
                           (uu____2152, f) in
                         FStar_Parser_AST.Project uu____2147 in
                       mk1 uu____2146
                   | uu____2153 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2154) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2174 =
               match new_args with
               | (a1,uu____2192)::(a2,uu____2194)::[] -> (a1, a2)
               | uu____2225 -> failwith "wrong arguments to try_with" in
             (match uu____2174 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2256 =
                      let uu____2257 = FStar_Syntax_Subst.compress term in
                      uu____2257.FStar_Syntax_Syntax.n in
                    match uu____2256 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2262) ->
                        let uu____2283 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2283 with | (x1,e2) -> e2)
                    | uu____2290 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2292 = decomp body in resugar_term uu____2292 in
                  let handler1 =
                    let uu____2294 = decomp handler in
                    resugar_term uu____2294 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2300,uu____2301,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2333,uu____2334,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2355 =
                          let uu____2356 =
                            let uu____2365 = resugar_body t11 in
                            (uu____2365, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2356 in
                        mk1 uu____2355
                    | uu____2368 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2423 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2453) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2459) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2544 -> (xs, pat, t1) in
             let resugar body =
               let uu____2555 =
                 let uu____2556 = FStar_Syntax_Subst.compress body in
                 uu____2556.FStar_Syntax_Syntax.n in
               match uu____2555 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2561) ->
                   let uu____2582 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2582 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2590 = FStar_Options.print_implicits () in
                          if uu____2590 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2599 =
                          let uu____2608 =
                            let uu____2609 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2609.FStar_Syntax_Syntax.n in
                          match uu____2608 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2678  ->
                                                 match uu____2678 with
                                                 | (e2,uu____2684) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2687) ->
                                    let uu____2688 =
                                      let uu____2691 =
                                        let uu____2692 = name s r in
                                        mk1 uu____2692 in
                                      [uu____2691] in
                                    [uu____2688]
                                | uu____2697 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2706 ->
                              let uu____2707 = resugar_term body2 in
                              ([], uu____2707) in
                        (match uu____2599 with
                         | (pats,body3) ->
                             let uu____2724 = uncurry xs3 pats body3 in
                             (match uu____2724 with
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
               | uu____2772 ->
                   if op = "forall"
                   then
                     let uu____2773 =
                       let uu____2774 =
                         let uu____2787 = resugar_term body in
                         ([], [[]], uu____2787) in
                       FStar_Parser_AST.QForall uu____2774 in
                     mk1 uu____2773
                   else
                     (let uu____2799 =
                        let uu____2800 =
                          let uu____2813 = resugar_term body in
                          ([], [[]], uu____2813) in
                        FStar_Parser_AST.QExists uu____2800 in
                      mk1 uu____2799) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____2840)::[] -> resugar b
                | uu____2857 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2867) ->
             let uu____2872 = FStar_List.hd args1 in
             (match uu____2872 with | (e1,uu____2886) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2931  ->
                       match uu____2931 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____2938 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____2938 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2945 =
                         let uu____2946 =
                           let uu____2953 =
                             let uu____2956 = last1 args1 in
                             resugar uu____2956 in
                           (op1, uu____2953) in
                         FStar_Parser_AST.Op uu____2946 in
                       mk1 uu____2945
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2971 =
                         let uu____2972 =
                           let uu____2979 =
                             let uu____2982 = last_two args1 in
                             resugar uu____2982 in
                           (op1, uu____2979) in
                         FStar_Parser_AST.Op uu____2972 in
                       mk1 uu____2971
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____2997 =
                         let uu____2998 =
                           let uu____3005 =
                             let uu____3008 = last_three args1 in
                             resugar uu____3008 in
                           (op1, uu____3005) in
                         FStar_Parser_AST.Op uu____2998 in
                       mk1 uu____2997
                   | uu____3017 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3024 =
                    let uu____3025 =
                      let uu____3032 =
                        let uu____3035 = last_two args1 in resugar uu____3035 in
                      (op1, uu____3032) in
                    FStar_Parser_AST.Op uu____3025 in
                  mk1 uu____3024
              | uu____3044 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3047,t1)::[]) ->
        let bnds =
          let uu____3120 =
            let uu____3125 = resugar_pat pat in
            let uu____3126 = resugar_term e in (uu____3125, uu____3126) in
          [uu____3120] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3144,t1)::(pat2,uu____3147,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3243 =
          let uu____3244 =
            let uu____3251 = resugar_term e in
            let uu____3252 = resugar_term t1 in
            let uu____3253 = resugar_term t2 in
            (uu____3251, uu____3252, uu____3253) in
          FStar_Parser_AST.If uu____3244 in
        mk1 uu____3243
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3311 =
          match uu____3311 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3342 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3342 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3346 =
          let uu____3347 =
            let uu____3362 = resugar_term e in
            let uu____3363 = FStar_List.map resugar_branch branches in
            (uu____3362, uu____3363) in
          FStar_Parser_AST.Match uu____3347 in
        mk1 uu____3346
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3403) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3470 =
          let uu____3471 =
            let uu____3480 = resugar_term e in (uu____3480, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3471 in
        mk1 uu____3470
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3504 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3504 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3529 =
                 let uu____3534 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3534 in
               match uu____3529 with
               | (univs1,td) ->
                   let uu____3545 =
                     let uu____3554 =
                       let uu____3555 = FStar_Syntax_Subst.compress td in
                       uu____3555.FStar_Syntax_Syntax.n in
                     match uu____3554 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3566,(t1,uu____3568)::(d,uu____3570)::[]) ->
                         (t1, d)
                     | uu____3613 -> failwith "wrong let binding format" in
                   (match uu____3545 with
                    | (typ,def) ->
                        let uu____3640 =
                          let uu____3647 =
                            let uu____3648 = FStar_Syntax_Subst.compress def in
                            uu____3648.FStar_Syntax_Syntax.n in
                          match uu____3647 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3659) ->
                              let uu____3680 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____3680 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3694 =
                                       FStar_Options.print_implicits () in
                                     if uu____3694 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____3696 -> ([], def, false) in
                        (match uu____3640 with
                         | (binders,term,is_pat_app) ->
                             let uu____3720 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3731 =
                                     let uu____3732 =
                                       let uu____3733 =
                                         let uu____3740 =
                                           bv_as_unique_ident bv in
                                         (uu____3740,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____3733 in
                                     mk_pat uu____3732 in
                                   (uu____3731, term) in
                             (match uu____3720 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____3776  ->
                                              match uu____3776 with
                                              | (bv,q) ->
                                                  let uu____3791 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____3791
                                                    (fun q1  ->
                                                       let uu____3803 =
                                                         let uu____3804 =
                                                           let uu____3811 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____3811, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3804 in
                                                       mk_pat uu____3803))) in
                                    let uu____3814 =
                                      let uu____3819 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3819) in
                                    let uu____3822 =
                                      universe_to_string univs1 in
                                    (uu____3814, uu____3822)
                                  else
                                    (let uu____3828 =
                                       let uu____3833 = resugar_term term1 in
                                       (pat, uu____3833) in
                                     let uu____3834 =
                                       universe_to_string univs1 in
                                     (uu____3828, uu____3834))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____3880 =
                   let uu____3881 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____3881 in
                 fun a363  ->
                   (Obj.magic
                      (if uu____3880
                       then FStar_Pervasives_Native.fst
                       else
                         (fun uu___188_3901  ->
                            match uu___188_3901 with
                            | ((pat,body2),univs1) ->
                                let uu____3921 =
                                  if univs1 = ""
                                  then body2
                                  else
                                    mk1
                                      (FStar_Parser_AST.Labeled
                                         (body2, univs1, true)) in
                                (pat, uu____3921)))) a363 in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3944) ->
        let s =
          let uu____3970 =
            let uu____3971 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____3971 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____3970 in
        let uu____3972 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____3972
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___189_3982 =
          match uu___189_3982 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4003 =
                  let uu____4004 = FStar_Syntax_Subst.compress h in
                  uu____4004.FStar_Syntax_Syntax.n in
                match uu____4003 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4024 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4024, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4047 = head_fv_universes_args h1 in
                    (match uu____4047 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4135 = head_fv_universes_args head1 in
                    (match uu____4135 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4207 ->
                    let uu____4208 =
                      let uu____4209 =
                        let uu____4210 =
                          let uu____4211 = resugar_term h in
                          parser_term_to_string uu____4211 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4210 in
                      FStar_Errors.Err uu____4209 in
                    FStar_Exn.raise uu____4208 in
              let uu____4228 =
                try
                  let uu____4280 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4280
                with
                | FStar_Errors.Err uu____4301 ->
                    let uu____4302 =
                      let uu____4303 =
                        let uu____4308 =
                          let uu____4309 =
                            let uu____4310 = resugar_term e in
                            parser_term_to_string uu____4310 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4309 in
                        (uu____4308, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4303 in
                    FStar_Exn.raise uu____4302 in
              (match uu____4228 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4364 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4364, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.map
                       (fun uu____4387  ->
                          match uu____4387 with
                          | (t1,q) ->
                              let uu____4404 = resugar_term t1 in
                              let uu____4405 = resugar_imp q in
                              (uu____4404, uu____4405)) args in
                   let args2 =
                     let uu____4413 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4415 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4415) in
                     if uu____4413
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4438,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4463 =
                      let uu____4464 =
                        let uu____4473 = resugar_seq t11 in
                        (uu____4473, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____4464 in
                    mk1 uu____4463
                | uu____4476 -> t1 in
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
               | uu____4498 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____4500 =
                let uu____4501 = FStar_Syntax_Subst.compress e in
                uu____4501.FStar_Syntax_Syntax.n in
              (match uu____4500 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4505;
                      FStar_Syntax_Syntax.vars = uu____4506;_},(term,uu____4508)::[])
                   -> resugar_term term
               | uu____4537 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4575  ->
                       match uu____4575 with
                       | (x,uu____4581) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4583,p) ->
             let uu____4585 =
               let uu____4586 =
                 let uu____4593 = resugar_term e in (uu____4593, l, p) in
               FStar_Parser_AST.Labeled uu____4586 in
             mk1 uu____4585
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4595,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4604 =
               let uu____4605 =
                 let uu____4614 = resugar_term e in
                 let uu____4615 =
                   let uu____4616 =
                     let uu____4617 =
                       let uu____4628 =
                         let uu____4635 =
                           let uu____4640 = resugar_term t1 in
                           (uu____4640, FStar_Parser_AST.Nothing) in
                         [uu____4635] in
                       (name1, uu____4628) in
                     FStar_Parser_AST.Construct uu____4617 in
                   mk1 uu____4616 in
                 (uu____4614, uu____4615, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4605 in
             mk1 uu____4604
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4658,t1) ->
             let uu____4664 =
               let uu____4665 =
                 let uu____4674 = resugar_term e in
                 let uu____4675 =
                   let uu____4676 =
                     let uu____4677 =
                       let uu____4688 =
                         let uu____4695 =
                           let uu____4700 = resugar_term t1 in
                           (uu____4700, FStar_Parser_AST.Nothing) in
                         [uu____4695] in
                       (name1, uu____4688) in
                     FStar_Parser_AST.Construct uu____4677 in
                   mk1 uu____4676 in
                 (uu____4674, uu____4675, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____4665 in
             mk1 uu____4664)
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
             let uu____4748 = FStar_Options.print_universes () in
             if uu____4748
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
             let uu____4809 = FStar_Options.print_universes () in
             if uu____4809
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
          let uu____4850 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____4850, FStar_Parser_AST.Nothing) in
        let uu____4851 = FStar_Options.print_effect_args () in
        if uu____4851
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___190_4908 =
                match uu___190_4908 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____4969 -> aux l tl1
                     | uu____4976 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5011  ->
                 match uu____5011 with
                 | (e,uu____5021) ->
                     let uu____5022 = resugar_term e in
                     (uu____5022, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___191_5043 =
            match uu___191_5043 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5076 = resugar_term e in
                       (uu____5076, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5081 -> aux l tl1) in
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
      let uu____5126 = b in
      match uu____5126 with
      | (x,aq) ->
          let uu____5131 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5131
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5145 =
                     let uu____5146 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5146 in
                   FStar_Parser_AST.mk_binder uu____5145 r
                     FStar_Parser_AST.Type_level imp
               | uu____5147 ->
                   let uu____5148 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5148
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5150 =
                        let uu____5151 =
                          let uu____5156 = bv_as_unique_ident x in
                          (uu____5156, e) in
                        FStar_Parser_AST.Annotated uu____5151 in
                      FStar_Parser_AST.mk_binder uu____5150 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5165 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5165 in
      let uu____5166 =
        let uu____5167 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5167.FStar_Syntax_Syntax.n in
      match uu____5166 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5175 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5175
          else
            (let uu____5177 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5177
               (fun aq  ->
                  let uu____5189 =
                    let uu____5190 =
                      let uu____5191 =
                        let uu____5198 = bv_as_unique_ident x in
                        (uu____5198, aq) in
                      FStar_Parser_AST.PatVar uu____5191 in
                    mk1 uu____5190 in
                  FStar_Pervasives_Native.Some uu____5189))
      | uu____5201 ->
          let uu____5202 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5202
            (fun aq  ->
               let pat =
                 let uu____5217 =
                   let uu____5218 =
                     let uu____5225 = bv_as_unique_ident x in
                     (uu____5225, aq) in
                   FStar_Parser_AST.PatVar uu____5218 in
                 mk1 uu____5217 in
               let uu____5228 = FStar_Options.print_bound_var_types () in
               if uu____5228
               then
                 let uu____5231 =
                   let uu____5232 =
                     let uu____5233 =
                       let uu____5238 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5238) in
                     FStar_Parser_AST.PatAscribed uu____5233 in
                   mk1 uu____5232 in
                 FStar_Pervasives_Native.Some uu____5231
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
              (fun uu____5315  ->
                 match uu____5315 with
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
              (fun uu____5350  ->
                 match uu____5350 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5357 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5357
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5363;
             FStar_Syntax_Syntax.fv_delta = uu____5364;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5391 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____5391 FStar_List.rev in
          let args1 =
            let uu____5407 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5427  ->
                      match uu____5427 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____5407 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5497 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5497
            | (hd1::tl1,hd2::tl2) ->
                let uu____5520 = map21 tl1 tl2 in (hd1, hd2) :: uu____5520 in
          let args2 =
            let uu____5538 = map21 fields1 args1 in
            FStar_All.pipe_right uu____5538 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5589  ->
                 match uu____5589 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5599 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____5599 with
           | FStar_Pervasives_Native.Some (op,uu____5607) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5616 =
                 let uu____5617 =
                   let uu____5624 = bv_as_unique_ident v1 in
                   let uu____5625 = to_arg_qual imp_opt in
                   (uu____5624, uu____5625) in
                 FStar_Parser_AST.PatVar uu____5617 in
               mk1 uu____5616)
      | FStar_Syntax_Syntax.Pat_wild uu____5630 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5638 =
              let uu____5639 =
                let uu____5646 = bv_as_unique_ident bv in
                (uu____5646,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____5639 in
            mk1 uu____5638 in
          let uu____5649 = FStar_Options.print_bound_var_types () in
          if uu____5649
          then
            let uu____5650 =
              let uu____5651 =
                let uu____5656 = resugar_term term in (pat, uu____5656) in
              FStar_Parser_AST.PatAscribed uu____5651 in
            mk1 uu____5650
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___192_5663  ->
    match uu___192_5663 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5672 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5673 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5674 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5679 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5688 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5697 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___193_5701  ->
    match uu___193_5701 with
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
          (tylid,uvs,bs,t,uu____5730,datacons) ->
          let uu____5740 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5767,uu____5768,uu____5769,inductive_lid,uu____5771,uu____5772)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5777 -> failwith "unexpected")) in
          (match uu____5740 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5796 = FStar_Options.print_implicits () in
                 if uu____5796 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____5806 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___194_5811  ->
                           match uu___194_5811 with
                           | FStar_Syntax_Syntax.RecordType uu____5812 ->
                               true
                           | uu____5821 -> false)) in
                 if uu____5806
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5869,univs1,term,uu____5872,num,uu____5874)
                         ->
                         let uu____5879 =
                           let uu____5880 = FStar_Syntax_Subst.compress term in
                           uu____5880.FStar_Syntax_Syntax.n in
                         (match uu____5879 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5894) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____5955  ->
                                        match uu____5955 with
                                        | (b,qual) ->
                                            let uu____5970 =
                                              let uu____5971 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____5971 in
                                            let uu____5972 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____5970, uu____5972,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____5983 -> failwith "unexpected")
                     | uu____5994 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6115,num,uu____6117) ->
                          let c =
                            let uu____6135 =
                              let uu____6138 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6138 in
                            ((l.FStar_Ident.ident), uu____6135,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6155 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6231 ->
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
        let uu____6252 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6252;
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
      let uu____6269 = ts in
      match uu____6269 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6277 =
            let uu____6278 =
              let uu____6291 =
                let uu____6300 =
                  let uu____6307 =
                    let uu____6308 =
                      let uu____6321 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6321) in
                    FStar_Parser_AST.TyconAbbrev uu____6308 in
                  (uu____6307, FStar_Pervasives_Native.None) in
                [uu____6300] in
              (false, uu____6291) in
            FStar_Parser_AST.Tycon uu____6278 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6277
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
            let uu____6380 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____6380 with
            | (bs,action_defn) ->
                let uu____6387 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____6387 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6395 = FStar_Options.print_implicits () in
                       if uu____6395
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____6400 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____6400 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____6414 =
                           let uu____6425 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____6425,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____6414 in
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
          let uu____6499 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____6499 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6507 = FStar_Options.print_implicits () in
                if uu____6507 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____6512 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____6512 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6570) ->
        let uu____6579 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6601 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6618 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6625 -> false
                  | uu____6640 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____6579 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6672 se1 =
               match uu____6672 with
               | (datacon_ses1,tycons) ->
                   let uu____6698 = resugar_typ datacon_ses1 se1 in
                   (match uu____6698 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____6713 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____6713 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6748 =
                         let uu____6749 =
                           let uu____6750 =
                             let uu____6763 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____6763) in
                           FStar_Parser_AST.Tycon uu____6750 in
                         decl'_to_decl se uu____6749 in
                       FStar_Pervasives_Native.Some uu____6748
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6794,uu____6795,uu____6796,uu____6797,uu____6798)
                            ->
                            let uu____6803 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____6803
                        | uu____6806 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6809 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6815) ->
        let uu____6820 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___195_6826  ->
                  match uu___195_6826 with
                  | FStar_Syntax_Syntax.Projector (uu____6827,uu____6828) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6829 -> true
                  | uu____6830 -> false)) in
        if uu____6820
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6853) ->
               let uu____6866 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____6866
           | uu____6873 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6877,fml) ->
        let uu____6879 =
          let uu____6880 =
            let uu____6881 =
              let uu____6886 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____6886) in
            FStar_Parser_AST.Assume uu____6881 in
          decl'_to_decl se uu____6880 in
        FStar_Pervasives_Native.Some uu____6879
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6888 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6888
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6890 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____6890
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6899,t) ->
              let uu____6911 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6911
          | uu____6912 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____6920,t) ->
              let uu____6932 = resugar_term t in
              FStar_Pervasives_Native.Some uu____6932
          | uu____6933 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____6957 -> failwith "Should not happen hopefully" in
        let uu____6966 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____6966
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____6976 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____6976 with
         | (bs1,c1) ->
             let bs2 =
               let uu____6986 = FStar_Options.print_implicits () in
               if uu____6986 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____6995 =
               let uu____6996 =
                 let uu____6997 =
                   let uu____7010 =
                     let uu____7019 =
                       let uu____7026 =
                         let uu____7027 =
                           let uu____7040 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7040) in
                         FStar_Parser_AST.TyconAbbrev uu____7027 in
                       (uu____7026, FStar_Pervasives_Native.None) in
                     [uu____7019] in
                   (false, uu____7010) in
                 FStar_Parser_AST.Tycon uu____6997 in
               decl'_to_decl se uu____6996 in
             FStar_Pervasives_Native.Some uu____6995)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7068 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7068
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7072 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_7078  ->
                  match uu___196_7078 with
                  | FStar_Syntax_Syntax.Projector (uu____7079,uu____7080) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7081 -> true
                  | uu____7082 -> false)) in
        if uu____7072
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7087 =
               (let uu____7090 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7090) || (FStar_List.isEmpty uvs) in
             if uu____7087
             then resugar_term t
             else
               (let uu____7092 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7092 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7100 =
                      let uu____7101 =
                        let uu____7108 = resugar_term t1 in
                        (uu____7108, universes, true) in
                      FStar_Parser_AST.Labeled uu____7101 in
                    FStar_Parser_AST.mk_term uu____7100
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____7109 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7109)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7110 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7127 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7142 -> FStar_Pervasives_Native.None