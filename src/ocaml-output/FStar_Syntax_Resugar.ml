open Prims
let doc_to_string: FStar_Pprint.document -> Prims.string =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
let parser_term_to_string: FStar_Parser_AST.term -> Prims.string =
  fun t  ->
    let uu____9 = FStar_Parser_ToDocument.term_to_document t in
    doc_to_string uu____9
let map_opt f l =
  let uu____43 =
    FStar_Util.choose_map
      (fun uu____53  -> fun x  -> let uu____55 = f x in ((), uu____55)) () l in
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
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___187_127  ->
          match uu___187_127 with
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
    let name_of_op uu___188_369 =
      match uu___188_369 with
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
        let uu____857 = string_to_op s in
        (match uu____857 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____883 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____900 -> FStar_Pervasives_Native.None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____909 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____914 -> true
    | uu____915 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____946 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____946 in
    let var a r =
      let uu____954 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____954 in
    let uu____955 =
      let uu____956 = FStar_Syntax_Subst.compress t in
      uu____956.FStar_Syntax_Syntax.n in
    match uu____955 with
    | FStar_Syntax_Syntax.Tm_delayed uu____961 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____992 = let uu____995 = bv_as_unique_ident x in [uu____995] in
          FStar_Ident.lid_of_ids uu____992 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____998 =
            let uu____1001 = bv_as_unique_ident x in [uu____1001] in
          FStar_Ident.lid_of_ids uu____998 in
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
          let uu____1019 =
            let uu____1020 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____1020 in
          mk1 uu____1019
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
             | uu____1030 -> failwith "wrong projector format")
          else
            (let uu____1034 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1037 =
                    let uu____1038 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____1038 in
                  let uu____1039 = FStar_String.get s (Prims.parse_int "0") in
                  uu____1037 <> uu____1039) in
             if uu____1034
             then
               let uu____1040 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____1040
             else
               (let uu____1042 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____1042))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1053 = FStar_Options.print_universes () in
        if uu____1053
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1060 =
                   let uu____1061 =
                     let uu____1068 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____1068, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1061 in
                 mk1 uu____1060) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1071 = FStar_Syntax_Syntax.is_teff t in
        if uu____1071
        then
          let uu____1072 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____1072
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1075 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1075
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1076 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____1076
         | uu____1077 ->
             let uu____1078 = FStar_Options.print_universes () in
             if uu____1078
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1096 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____1096))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1099) ->
        let uu____1124 = FStar_Syntax_Subst.open_term xs body in
        (match uu____1124 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1132 = FStar_Options.print_implicits () in
               if uu____1132 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1146  ->
                       match uu____1146 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1180 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____1180 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1188 = FStar_Options.print_implicits () in
               if uu____1188 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____1194 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____1194 FStar_List.rev in
             let rec aux body3 uu___189_1213 =
               match uu___189_1213 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1233 =
          let uu____1238 =
            let uu____1239 = FStar_Syntax_Syntax.mk_binder x in [uu____1239] in
          FStar_Syntax_Subst.open_term uu____1238 phi in
        (match uu____1233 with
         | (x1,phi1) ->
             let b =
               let uu____1243 =
                 let uu____1246 = FStar_List.hd x1 in
                 resugar_binder uu____1246 t.FStar_Syntax_Syntax.pos in
               FStar_Util.must uu____1243 in
             let uu____1251 =
               let uu____1252 =
                 let uu____1257 = resugar_term phi1 in (b, uu____1257) in
               FStar_Parser_AST.Refine uu____1252 in
             mk1 uu____1251)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___190_1311 =
          match uu___190_1311 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1401 -> failwith "last of an empty list" in
        let rec last_two uu___191_1445 =
          match uu___191_1445 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1484::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1585::t1 -> last_two t1 in
        let rec last_three uu___192_1636 =
          match uu___192_1636 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1675::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1710::uu____1711::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1853::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1945  ->
                    match uu____1945 with
                    | (e2,qual) ->
                        let uu____1964 = resugar_term e2 in
                        (uu____1964, qual))) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1980  ->
                 match uu____1980 with
                 | (x,qual) ->
                     let uu____1993 =
                       let uu____1994 =
                         let uu____2001 = resugar_imp qual in
                         (acc, x, uu____2001) in
                       FStar_Parser_AST.App uu____1994 in
                     mk1 uu____1993) e2 args2 in
        let args1 =
          let uu____2013 = FStar_Options.print_implicits () in
          if uu____2013 then args else filter_imp args in
        let uu____2029 = resugar_term_as_op e in
        (match uu____2029 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____2040) ->
             (match args1 with
              | (fst1,uu____2046)::(snd1,uu____2048)::rest ->
                  let e1 =
                    let uu____2093 =
                      let uu____2094 =
                        let uu____2101 =
                          let uu____2104 = resugar_term fst1 in
                          let uu____2105 =
                            let uu____2108 = resugar_term snd1 in
                            [uu____2108] in
                          uu____2104 :: uu____2105 in
                        ((FStar_Ident.id_of_text "*"), uu____2101) in
                      FStar_Parser_AST.Op uu____2094 in
                    mk1 uu____2093 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____2121  ->
                         match uu____2121 with
                         | (x,uu____2127) ->
                             let uu____2128 =
                               let uu____2129 =
                                 let uu____2136 =
                                   let uu____2139 =
                                     let uu____2142 = resugar_term x in
                                     [uu____2142] in
                                   e1 :: uu____2139 in
                                 ((FStar_Ident.id_of_text "*"), uu____2136) in
                               FStar_Parser_AST.Op uu____2129 in
                             mk1 uu____2128) e1 rest
              | uu____2145 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2156) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____2190)::[] -> b
               | uu____2215 -> failwith "wrong arguments to dtuple" in
             let uu____2230 =
               let uu____2231 = FStar_Syntax_Subst.compress body in
               uu____2231.FStar_Syntax_Syntax.n in
             (match uu____2230 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2238) ->
                  let uu____2263 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____2263 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2271 = FStar_Options.print_implicits () in
                         if uu____2271 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2283 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2306  ->
                            match uu____2306 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2318) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2324) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2329 = FStar_List.hd args1 in
             (match uu____2329 with
              | (t1,uu____2347) ->
                  let uu____2356 =
                    let uu____2357 = FStar_Syntax_Subst.compress t1 in
                    uu____2357.FStar_Syntax_Syntax.n in
                  (match uu____2356 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____2364 =
                         let uu____2365 =
                           let uu____2370 = resugar_term t1 in
                           (uu____2370, f) in
                         FStar_Parser_AST.Project uu____2365 in
                       mk1 uu____2364
                   | uu____2371 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2372) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____2396 =
               match new_args with
               | (a1,uu____2422)::(a2,uu____2424)::[] -> (a1, a2)
               | uu____2473 -> failwith "wrong arguments to try_with" in
             (match uu____2396 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2518 =
                      let uu____2519 = FStar_Syntax_Subst.compress term in
                      uu____2519.FStar_Syntax_Syntax.n in
                    match uu____2518 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2526) ->
                        let uu____2551 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____2551 with | (x1,e2) -> e2)
                    | uu____2558 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____2560 = decomp body in resugar_term uu____2560 in
                  let handler1 =
                    let uu____2562 = decomp handler in
                    resugar_term uu____2562 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2568,uu____2569,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2601,uu____2602,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2623 =
                          let uu____2624 =
                            let uu____2633 = resugar_body t11 in
                            (uu____2633, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____2624 in
                        mk1 uu____2623
                    | uu____2636 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2691 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2721) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2727) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2812 -> (xs, pat, t1) in
             let resugar body =
               let uu____2823 =
                 let uu____2824 = FStar_Syntax_Subst.compress body in
                 uu____2824.FStar_Syntax_Syntax.n in
               match uu____2823 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2831) ->
                   let uu____2856 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____2856 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2864 = FStar_Options.print_implicits () in
                          if uu____2864 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____2873 =
                          let uu____2882 =
                            let uu____2883 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____2883.FStar_Syntax_Syntax.n in
                          match uu____2882 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2960  ->
                                                 match uu____2960 with
                                                 | (e2,uu____2966) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2969) ->
                                    let uu____2970 =
                                      let uu____2973 =
                                        let uu____2974 = name s r in
                                        mk1 uu____2974 in
                                      [uu____2973] in
                                    [uu____2970]
                                | uu____2979 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____2988 ->
                              let uu____2989 = resugar_term body2 in
                              ([], uu____2989) in
                        (match uu____2873 with
                         | (pats,body3) ->
                             let uu____3006 = uncurry xs3 pats body3 in
                             (match uu____3006 with
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
               | uu____3054 ->
                   if op = "forall"
                   then
                     let uu____3055 =
                       let uu____3056 =
                         let uu____3069 = resugar_term body in
                         ([], [[]], uu____3069) in
                       FStar_Parser_AST.QForall uu____3056 in
                     mk1 uu____3055
                   else
                     (let uu____3081 =
                        let uu____3082 =
                          let uu____3095 = resugar_term body in
                          ([], [[]], uu____3095) in
                        FStar_Parser_AST.QExists uu____3082 in
                      mk1 uu____3081) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____3126)::[] -> resugar b
                | uu____3151 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____3163) ->
             let uu____3168 = FStar_List.hd args1 in
             (match uu____3168 with | (e1,uu____3186) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____3235  ->
                       match uu____3235 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____3242 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____3242 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____3251 =
                         let uu____3252 =
                           let uu____3259 =
                             let uu____3262 = last1 args1 in
                             resugar uu____3262 in
                           (op1, uu____3259) in
                         FStar_Parser_AST.Op uu____3252 in
                       mk1 uu____3251
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____3279 =
                         let uu____3280 =
                           let uu____3287 =
                             let uu____3290 = last_two args1 in
                             resugar uu____3290 in
                           (op1, uu____3287) in
                         FStar_Parser_AST.Op uu____3280 in
                       mk1 uu____3279
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3307 =
                         let uu____3308 =
                           let uu____3315 =
                             let uu____3318 = last_three args1 in
                             resugar uu____3318 in
                           (op1, uu____3315) in
                         FStar_Parser_AST.Op uu____3308 in
                       mk1 uu____3307
                   | uu____3327 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3336 =
                    let uu____3337 =
                      let uu____3344 =
                        let uu____3347 = last_two args1 in resugar uu____3347 in
                      (op1, uu____3344) in
                    FStar_Parser_AST.Op uu____3337 in
                  mk1 uu____3336
              | uu____3356 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3359,t1)::[]) ->
        let bnds =
          let uu____3456 =
            let uu____3461 = resugar_pat pat in
            let uu____3462 = resugar_term e in (uu____3461, uu____3462) in
          [uu____3456] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3480,t1)::(pat2,uu____3483,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3615 =
          let uu____3616 =
            let uu____3623 = resugar_term e in
            let uu____3624 = resugar_term t1 in
            let uu____3625 = resugar_term t2 in
            (uu____3623, uu____3624, uu____3625) in
          FStar_Parser_AST.If uu____3616 in
        mk1 uu____3615
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3695 =
          match uu____3695 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3726 = resugar_term e1 in
                    FStar_Pervasives_Native.Some uu____3726 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____3730 =
          let uu____3731 =
            let uu____3746 = resugar_term e in
            let uu____3747 = FStar_List.map resugar_branch branches in
            (uu____3746, uu____3747) in
          FStar_Parser_AST.Match uu____3731 in
        mk1 uu____3730
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3787) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____3888 =
          let uu____3889 =
            let uu____3898 = resugar_term e in (uu____3898, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____3889 in
        mk1 uu____3888
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____3926 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____3926 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3951 =
                 let uu____3956 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3956 in
               match uu____3951 with
               | (univs1,td) ->
                   let uu____3967 =
                     let uu____3980 =
                       let uu____3981 = FStar_Syntax_Subst.compress td in
                       uu____3981.FStar_Syntax_Syntax.n in
                     match uu____3980 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3998,(t1,uu____4000)::(d,uu____4002)::[]) ->
                         (t1, d)
                     | uu____4069 -> failwith "wrong let binding format" in
                   (match uu____3967 with
                    | (typ,def) ->
                        let uu____4108 =
                          let uu____4115 =
                            let uu____4116 = FStar_Syntax_Subst.compress def in
                            uu____4116.FStar_Syntax_Syntax.n in
                          match uu____4115 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4129) ->
                              let uu____4154 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____4154 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____4168 =
                                       FStar_Options.print_implicits () in
                                     if uu____4168 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____4170 -> ([], def, false) in
                        (match uu____4108 with
                         | (binders,term,is_pat_app) ->
                             let uu____4196 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____4207 =
                                     let uu____4208 =
                                       let uu____4209 =
                                         let uu____4216 =
                                           bv_as_unique_ident bv in
                                         (uu____4216,
                                           FStar_Pervasives_Native.None) in
                                       FStar_Parser_AST.PatVar uu____4209 in
                                     mk_pat uu____4208 in
                                   (uu____4207, term) in
                             (match uu____4196 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____4252  ->
                                              match uu____4252 with
                                              | (bv,q) ->
                                                  let uu____4267 =
                                                    resugar_arg_qual q in
                                                  FStar_Util.map_opt
                                                    uu____4267
                                                    (fun q1  ->
                                                       let uu____4279 =
                                                         let uu____4280 =
                                                           let uu____4287 =
                                                             bv_as_unique_ident
                                                               bv in
                                                           (uu____4287, q1) in
                                                         FStar_Parser_AST.PatVar
                                                           uu____4280 in
                                                       mk_pat uu____4279))) in
                                    let uu____4290 =
                                      let uu____4295 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____4295) in
                                    let uu____4298 =
                                      universe_to_string univs1 in
                                    (uu____4290, uu____4298)
                                  else
                                    (let uu____4304 =
                                       let uu____4309 = resugar_term term1 in
                                       (pat, uu____4309) in
                                     let uu____4310 =
                                       universe_to_string univs1 in
                                     (uu____4304, uu____4310))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 =
               let f =
                 let uu____4356 =
                   let uu____4357 = FStar_Options.print_universes () in
                   Prims.op_Negation uu____4357 in
                 Obj.magic
                   (if uu____4356
                    then FStar_Pervasives_Native.fst
                    else
                      (fun uu___193_4377  ->
                         match uu___193_4377 with
                         | ((pat,body2),univs1) ->
                             let uu____4397 =
                               if univs1 = ""
                               then body2
                               else
                                 mk1
                                   (FStar_Parser_AST.Labeled
                                      (body2, univs1, true)) in
                             (pat, uu____4397))) in
               FStar_List.map f r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____4420) ->
        let s =
          let uu____4454 =
            let uu____4455 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____4455 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____4454 in
        let uu____4456 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____4456
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___194_4470 =
          match uu___194_4470 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4493 =
                  let uu____4494 = FStar_Syntax_Subst.compress h in
                  uu____4494.FStar_Syntax_Syntax.n in
                match uu____4493 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4518 = FStar_Syntax_Syntax.lid_of_fv fv in
                    (uu____4518, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4549 = head_fv_universes_args h1 in
                    (match uu____4549 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4655 = head_fv_universes_args head1 in
                    (match uu____4655 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4739 ->
                    let uu____4740 =
                      let uu____4741 =
                        let uu____4742 =
                          let uu____4743 = resugar_term h in
                          parser_term_to_string uu____4743 in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4742 in
                      FStar_Errors.Err uu____4741 in
                    raise uu____4740 in
              let uu____4762 =
                try
                  let uu____4820 = FStar_Syntax_Util.unmeta e in
                  head_fv_universes_args uu____4820
                with
                | FStar_Errors.Err uu____4843 ->
                    let uu____4844 =
                      let uu____4845 =
                        let uu____4850 =
                          let uu____4851 =
                            let uu____4852 = resugar_term e in
                            parser_term_to_string uu____4852 in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4851 in
                        (uu____4850, (e.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4845 in
                    raise uu____4844 in
              (match uu____4762 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4912 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos in
                          (uu____4912, FStar_Parser_AST.UnivApp)) universes in
                   let args1 =
                     FStar_List.map
                       (fun uu____4935  ->
                          match uu____4935 with
                          | (t1,q) ->
                              let uu____4952 = resugar_term t1 in
                              let uu____4953 = resugar_imp q in
                              (uu____4952, uu____4953)) args in
                   let args2 =
                     let uu____4961 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4963 = FStar_Options.print_universes () in
                          Prims.op_Negation uu____4963) in
                     if uu____4961
                     then args1
                     else FStar_List.append universes1 args1 in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4986,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____5011 =
                      let uu____5012 =
                        let uu____5021 = resugar_seq t11 in
                        (uu____5021, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____5012 in
                    mk1 uu____5011
                | uu____5024 -> t1 in
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
               | uu____5046 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              let uu____5048 =
                let uu____5049 = FStar_Syntax_Subst.compress e in
                uu____5049.FStar_Syntax_Syntax.n in
              (match uu____5048 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____5055;
                      FStar_Syntax_Syntax.pos = uu____5056;
                      FStar_Syntax_Syntax.vars = uu____5057;_},(term,uu____5059)::[])
                   -> resugar_term term
               | uu____5102 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____5146  ->
                       match uu____5146 with
                       | (x,uu____5152) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____5154,p) ->
             let uu____5156 =
               let uu____5157 =
                 let uu____5164 = resugar_term e in (uu____5164, l, p) in
               FStar_Parser_AST.Labeled uu____5157 in
             mk1 uu____5156
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____5166,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____5179 =
               let uu____5180 =
                 let uu____5189 = resugar_term e in
                 let uu____5190 =
                   let uu____5191 =
                     let uu____5192 =
                       let uu____5203 =
                         let uu____5210 =
                           let uu____5215 = resugar_term t1 in
                           (uu____5215, FStar_Parser_AST.Nothing) in
                         [uu____5210] in
                       (name1, uu____5203) in
                     FStar_Parser_AST.Construct uu____5192 in
                   mk1 uu____5191 in
                 (uu____5189, uu____5190, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____5180 in
             mk1 uu____5179
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5233,t1) ->
             let uu____5243 =
               let uu____5244 =
                 let uu____5253 = resugar_term e in
                 let uu____5254 =
                   let uu____5255 =
                     let uu____5256 =
                       let uu____5267 =
                         let uu____5274 =
                           let uu____5279 = resugar_term t1 in
                           (uu____5279, FStar_Parser_AST.Nothing) in
                         [uu____5274] in
                       (name1, uu____5267) in
                     FStar_Parser_AST.Construct uu____5256 in
                   mk1 uu____5255 in
                 (uu____5253, uu____5254, FStar_Pervasives_Native.None) in
               FStar_Parser_AST.Ascribed uu____5244 in
             mk1 uu____5243)
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
             let uu____5331 = FStar_Options.print_universes () in
             if uu____5331
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
             let uu____5396 = FStar_Options.print_universes () in
             if uu____5396
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
          let uu____5437 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____5437, FStar_Parser_AST.Nothing) in
        let uu____5438 = FStar_Options.print_effect_args () in
        if uu____5438
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Parser_Const.effect_Lemma_lid
            then
              let rec aux l uu___195_5505 =
                match uu___195_5505 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____5584 -> aux l tl1
                     | uu____5593 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____5634  ->
                 match uu____5634 with
                 | (e,uu____5644) ->
                     let uu____5645 = resugar_term e in
                     (uu____5645, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___196_5666 =
            match uu___196_5666 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5701 = resugar_term e in
                       (uu____5701, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____5706 -> aux l tl1) in
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
      let uu____5751 = b in
      match uu____5751 with
      | (x,aq) ->
          let uu____5756 = resugar_arg_qual aq in
          FStar_Util.map_opt uu____5756
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5770 =
                     let uu____5771 = bv_as_unique_ident x in
                     FStar_Parser_AST.Variable uu____5771 in
                   FStar_Parser_AST.mk_binder uu____5770 r
                     FStar_Parser_AST.Type_level imp
               | uu____5772 ->
                   let uu____5773 = FStar_Syntax_Syntax.is_null_bv x in
                   if uu____5773
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5775 =
                        let uu____5776 =
                          let uu____5781 = bv_as_unique_ident x in
                          (uu____5781, e) in
                        FStar_Parser_AST.Annotated uu____5776 in
                      FStar_Parser_AST.mk_binder uu____5775 r
                        FStar_Parser_AST.Type_level imp))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5790 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____5790 in
      let uu____5791 =
        let uu____5792 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____5792.FStar_Syntax_Syntax.n in
      match uu____5791 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____5802 = mk1 FStar_Parser_AST.PatWild in
            FStar_Pervasives_Native.Some uu____5802
          else
            (let uu____5804 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____5804
               (fun aq  ->
                  let uu____5816 =
                    let uu____5817 =
                      let uu____5818 =
                        let uu____5825 = bv_as_unique_ident x in
                        (uu____5825, aq) in
                      FStar_Parser_AST.PatVar uu____5818 in
                    mk1 uu____5817 in
                  FStar_Pervasives_Native.Some uu____5816))
      | uu____5828 ->
          let uu____5829 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____5829
            (fun aq  ->
               let pat =
                 let uu____5844 =
                   let uu____5845 =
                     let uu____5852 = bv_as_unique_ident x in
                     (uu____5852, aq) in
                   FStar_Parser_AST.PatVar uu____5845 in
                 mk1 uu____5844 in
               let uu____5855 = FStar_Options.print_bound_var_types () in
               if uu____5855
               then
                 let uu____5858 =
                   let uu____5859 =
                     let uu____5860 =
                       let uu____5865 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____5865) in
                     FStar_Parser_AST.PatAscribed uu____5860 in
                   mk1 uu____5859 in
                 FStar_Pervasives_Native.Some uu____5858
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
              (fun uu____5942  ->
                 match uu____5942 with
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
              (fun uu____5977  ->
                 match uu____5977 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          let uu____5984 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____5984
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5990;
             FStar_Syntax_Syntax.fv_delta = uu____5991;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____6018 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____6018 FStar_List.rev in
          let args1 =
            let uu____6034 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6054  ->
                      match uu____6054 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b))) in
            FStar_All.pipe_right uu____6034 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____6124 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6124
            | (hd1::tl1,hd2::tl2) ->
                let uu____6147 = map21 tl1 tl2 in (hd1, hd2) :: uu____6147 in
          let args2 =
            let uu____6165 = map21 fields1 args1 in
            FStar_All.pipe_right uu____6165 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____6216  ->
                 match uu____6216 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____6226 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____6226 with
           | FStar_Pervasives_Native.Some (op,uu____6234) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____6243 =
                 let uu____6244 =
                   let uu____6251 = bv_as_unique_ident v1 in
                   let uu____6252 = to_arg_qual imp_opt in
                   (uu____6251, uu____6252) in
                 FStar_Parser_AST.PatVar uu____6244 in
               mk1 uu____6243)
      | FStar_Syntax_Syntax.Pat_wild uu____6257 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____6269 =
              let uu____6270 =
                let uu____6277 = bv_as_unique_ident bv in
                (uu____6277,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)) in
              FStar_Parser_AST.PatVar uu____6270 in
            mk1 uu____6269 in
          let uu____6280 = FStar_Options.print_bound_var_types () in
          if uu____6280
          then
            let uu____6281 =
              let uu____6282 =
                let uu____6287 = resugar_term term in (pat, uu____6287) in
              FStar_Parser_AST.PatAscribed uu____6282 in
            mk1 uu____6281
          else pat in
    aux p FStar_Pervasives_Native.None
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___197_6294  ->
    match uu___197_6294 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6303 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6304 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6305 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6310 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6319 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6328 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___198_6332  ->
    match uu___198_6332 with
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
          (tylid,uvs,bs,t,uu____6361,datacons) ->
          let uu____6371 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____6398,uu____6399,uu____6400,inductive_lid,uu____6402,uu____6403)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____6408 -> failwith "unexpected")) in
          (match uu____6371 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____6427 = FStar_Options.print_implicits () in
                 if uu____6427 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____6437 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___199_6442  ->
                           match uu___199_6442 with
                           | FStar_Syntax_Syntax.RecordType uu____6443 ->
                               true
                           | uu____6452 -> false)) in
                 if uu____6437
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____6500,univs1,term,uu____6503,num,uu____6505)
                         ->
                         let uu____6510 =
                           let uu____6511 = FStar_Syntax_Subst.compress term in
                           uu____6511.FStar_Syntax_Syntax.n in
                         (match uu____6510 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6527) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____6592  ->
                                        match uu____6592 with
                                        | (b,qual) ->
                                            let uu____6607 =
                                              let uu____6608 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____6608 in
                                            let uu____6609 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____6607, uu____6609,
                                              FStar_Pervasives_Native.None))) in
                              FStar_List.append mfields fields
                          | uu____6620 -> failwith "unexpected")
                     | uu____6631 -> failwith "unexpected" in
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
                          (l,univs1,term,uu____6752,num,uu____6754) ->
                          let c =
                            let uu____6772 =
                              let uu____6775 = resugar_term term in
                              FStar_Pervasives_Native.Some uu____6775 in
                            ((l.FStar_Ident.ident), uu____6772,
                              FStar_Pervasives_Native.None, false) in
                          c :: constructors
                      | uu____6792 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors)) in
               (other_datacons, tyc))
      | uu____6868 ->
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
        let uu____6889 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6889;
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
      let uu____6906 = ts in
      match uu____6906 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____6914 =
            let uu____6915 =
              let uu____6928 =
                let uu____6937 =
                  let uu____6944 =
                    let uu____6945 =
                      let uu____6958 = resugar_term typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____6958) in
                    FStar_Parser_AST.TyconAbbrev uu____6945 in
                  (uu____6944, FStar_Pervasives_Native.None) in
                [uu____6937] in
              (false, uu____6928) in
            FStar_Parser_AST.Tycon uu____6915 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6914
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
            let uu____7017 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____7017 with
            | (bs,action_defn) ->
                let uu____7024 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____7024 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____7032 = FStar_Options.print_implicits () in
                       if uu____7032
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____7037 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____7037 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____7051 =
                           let uu____7062 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____7062,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____7051 in
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
          let uu____7136 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____7136 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____7144 = FStar_Options.print_implicits () in
                if uu____7144 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____7149 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____7149 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7207) ->
        let uu____7216 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____7238 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____7255 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____7262 -> false
                  | uu____7277 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____7216 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____7309 se1 =
               match uu____7309 with
               | (datacon_ses1,tycons) ->
                   let uu____7335 = resugar_typ datacon_ses1 se1 in
                   (match uu____7335 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____7350 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____7350 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____7385 =
                         let uu____7386 =
                           let uu____7387 =
                             let uu____7400 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons in
                             (false, uu____7400) in
                           FStar_Parser_AST.Tycon uu____7387 in
                         decl'_to_decl se uu____7386 in
                       FStar_Pervasives_Native.Some uu____7385
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____7431,uu____7432,uu____7433,uu____7434,uu____7435)
                            ->
                            let uu____7440 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None)) in
                            FStar_Pervasives_Native.Some uu____7440
                        | uu____7443 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____7446 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____7452) ->
        let uu____7457 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___200_7463  ->
                  match uu___200_7463 with
                  | FStar_Syntax_Syntax.Projector (uu____7464,uu____7465) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7466 -> true
                  | uu____7467 -> false)) in
        if uu____7457
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____7498) ->
               let uu____7511 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               FStar_Pervasives_Native.Some uu____7511
           | uu____7518 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____7522,fml) ->
        let uu____7524 =
          let uu____7525 =
            let uu____7526 =
              let uu____7531 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____7531) in
            FStar_Parser_AST.Assume uu____7526 in
          decl'_to_decl se uu____7525 in
        FStar_Pervasives_Native.Some uu____7524
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____7533 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7533
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____7535 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        FStar_Pervasives_Native.Some uu____7535
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____7544,t) ->
              let uu____7556 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7556
          | uu____7557 -> FStar_Pervasives_Native.None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____7565,t) ->
              let uu____7577 = resugar_term t in
              FStar_Pervasives_Native.Some uu____7577
          | uu____7578 -> FStar_Pervasives_Native.None in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____7602 -> failwith "Should not happen hopefully" in
        let uu____7611 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        FStar_Pervasives_Native.Some uu____7611
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____7621 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____7621 with
         | (bs1,c1) ->
             let bs2 =
               let uu____7631 = FStar_Options.print_implicits () in
               if uu____7631 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____7640 =
               let uu____7641 =
                 let uu____7642 =
                   let uu____7655 =
                     let uu____7664 =
                       let uu____7671 =
                         let uu____7672 =
                           let uu____7685 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7685) in
                         FStar_Parser_AST.TyconAbbrev uu____7672 in
                       (uu____7671, FStar_Pervasives_Native.None) in
                     [uu____7664] in
                   (false, uu____7655) in
                 FStar_Parser_AST.Tycon uu____7642 in
               decl'_to_decl se uu____7641 in
             FStar_Pervasives_Native.Some uu____7640)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7713 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        FStar_Pervasives_Native.Some uu____7713
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7717 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___201_7723  ->
                  match uu___201_7723 with
                  | FStar_Syntax_Syntax.Projector (uu____7724,uu____7725) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7726 -> true
                  | uu____7727 -> false)) in
        if uu____7717
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7732 =
               (let uu____7735 = FStar_Options.print_universes () in
                Prims.op_Negation uu____7735) || (FStar_List.isEmpty uvs) in
             if uu____7732
             then resugar_term t
             else
               (let uu____7737 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____7737 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1 in
                    let uu____7745 =
                      let uu____7746 =
                        let uu____7753 = resugar_term t1 in
                        (uu____7753, universes, true) in
                      FStar_Parser_AST.Labeled uu____7746 in
                    FStar_Parser_AST.mk_term uu____7745
                      t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un) in
           let uu____7754 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t')) in
           FStar_Pervasives_Native.Some uu____7754)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7755 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7772 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7787 -> FStar_Pervasives_Native.None