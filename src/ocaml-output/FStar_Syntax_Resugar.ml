open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.of_int (100)) doc
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____15 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____15
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____23 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____23
  
let map_opt :
  'Auu____33 'Auu____34 .
    unit ->
      ('Auu____33 -> 'Auu____34 FStar_Pervasives_Native.option) ->
        'Auu____33 Prims.list -> 'Auu____34 Prims.list
  = fun uu____50  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____59 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____59
      then
        let uu____63 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____63
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____73 .
    ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_128  ->
            match uu___0_128 with
            | (uu____136,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____143,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____144)) -> false
            | (uu____149,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____150)) -> false
            | uu____156 -> true))
  
let filter_pattern_imp :
  'Auu____169 .
    ('Auu____169 * Prims.bool) Prims.list ->
      ('Auu____169 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____204  ->
         match uu____204 with
         | (uu____211,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
  
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe))
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + Prims.int_one) u1
      | uu____261 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____274 = FStar_Options.print_universes ()  in
    if uu____274
    then
      let uu____278 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____278 (FStar_String.concat ", ")
    else ""
  
let rec (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____327 ->
          let uu____328 = universe_to_int Prims.int_zero u  in
          (match uu____328 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____339 =
                      let uu____340 =
                        let uu____341 =
                          let uu____353 = FStar_Util.string_of_int n1  in
                          (uu____353, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____341  in
                      FStar_Parser_AST.Const uu____340  in
                    mk1 uu____339 r
                | uu____366 ->
                    let e1 =
                      let uu____368 =
                        let uu____369 =
                          let uu____370 =
                            let uu____382 = FStar_Util.string_of_int n1  in
                            (uu____382, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____370  in
                        FStar_Parser_AST.Const uu____369  in
                      mk1 uu____368 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____396 =
                      let uu____397 =
                        let uu____404 = FStar_Ident.id_of_text "+"  in
                        (uu____404, [e1; e2])  in
                      FStar_Parser_AST.Op uu____397  in
                    mk1 uu____396 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____412 ->
               let t =
                 let uu____416 =
                   let uu____417 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____417  in
                 mk1 uu____416 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____426 =
                        let uu____427 =
                          let uu____434 = resugar_universe x r  in
                          (acc, uu____434, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____427  in
                      mk1 uu____426 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____436 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____448 =
              let uu____454 =
                let uu____456 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____456  in
              (uu____454, r)  in
            FStar_Ident.mk_ident uu____448  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
  
let (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env  -> fun u  -> fun r  -> resugar_universe u r 
let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___1_510 =
      match uu___1_510 with
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
            ("-", (FStar_Pervasives_Native.Some (Prims.of_int (2))))
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
      | uu____838 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".[||]<-", FStar_Pervasives_Native.None)
    | "op_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".(||)<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Access" ->
        FStar_Pervasives_Native.Some (".[||]", FStar_Pervasives_Native.None)
    | "op_Lens_Access" ->
        FStar_Pervasives_Native.Some (".(||)", FStar_Pervasives_Native.None)
    | uu____978 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____996 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____996 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1014 ->
               let maybeop =
                 let uu____1022 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1088)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1022
                  in
               FStar_Util.map_opt maybeop
                 (fun o  -> (o, FStar_Pervasives_Native.None)))
        else FStar_Pervasives_Native.None
  
type expected_arity = Prims.int FStar_Pervasives_Native.option
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string * expected_arity) FStar_Pervasives_Native.option)
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
      (FStar_Parser_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____1420 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1420 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1490 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = Prims.int_zero
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + Prims.int_one)
             in
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
                (let uu____1592 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1592
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1628 =
      let uu____1629 = FStar_Syntax_Subst.compress t  in
      uu____1629.FStar_Syntax_Syntax.n  in
    match uu____1628 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = Prims.int_zero
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + Prims.int_one)
           in
        let uu____1650 = string_to_op s  in
        (match uu____1650 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1690 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1707 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1724 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1735 -> true
    | uu____1737 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1758 ->
        let uu____1760 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1760
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1774 = may_shorten lid  in
      if uu____1774 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____1919 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1919  in
      let uu____1922 =
        let uu____1923 = FStar_Syntax_Subst.compress t  in
        uu____1923.FStar_Syntax_Syntax.n  in
      match uu____1922 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1926 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1951 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1951
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1954 =
              let uu____1957 = bv_as_unique_ident x  in [uu____1957]  in
            FStar_Ident.lid_of_ids uu____1954  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1960 =
              let uu____1963 = bv_as_unique_ident x  in [uu____1963]  in
            FStar_Ident.lid_of_ids uu____1960  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length1 = Prims.int_zero
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length1 + Prims.int_one)
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____1982 =
              let uu____1983 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1983  in
            mk1 uu____1982
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
            then
              (let rest =
                 FStar_Util.substring_from s
                   (FStar_String.length
                      FStar_Syntax_Util.field_projector_prefix)
                  in
               let r =
                 FStar_Util.split rest FStar_Syntax_Util.field_projector_sep
                  in
               match r with
               | fst1::snd1::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos
                      in
                   let r1 =
                     FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos))
                      in
                   mk1 (FStar_Parser_AST.Projector (l, r1))
               | uu____2007 -> failwith "wrong projector format")
            else
              (let uu____2014 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2014
               then
                 let uu____2017 =
                   let uu____2018 =
                     let uu____2019 =
                       let uu____2025 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2025)  in
                     FStar_Ident.mk_ident uu____2019  in
                   FStar_Parser_AST.Tvar uu____2018  in
                 mk1 uu____2017
               else
                 (let uu____2030 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2030
                  then
                    let uu____2033 =
                      let uu____2034 =
                        let uu____2035 =
                          let uu____2041 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2041)  in
                        FStar_Ident.mk_ident uu____2035  in
                      FStar_Parser_AST.Tvar uu____2034  in
                    mk1 uu____2033
                  else
                    (let uu____2046 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2050 =
                            let uu____2052 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2052  in
                          let uu____2055 = FStar_String.get s Prims.int_zero
                             in
                          uu____2050 <> uu____2055)
                        in
                     if uu____2046
                     then
                       let uu____2060 =
                         let uu____2061 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2061  in
                       mk1 uu____2060
                     else
                       (let uu____2064 =
                          let uu____2065 =
                            let uu____2076 = maybe_shorten_fv env fv  in
                            (uu____2076, [])  in
                          FStar_Parser_AST.Construct uu____2065  in
                        mk1 uu____2064))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2094 = FStar_Options.print_universes ()  in
          if uu____2094
          then
            let univs1 =
              FStar_List.map
                (fun x  -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes
               in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1,args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____2125 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2125  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2148 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2156 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2156
          then
            let uu____2159 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2159
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2164 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2185 -> ("Type", true)  in
          (match uu____2164 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2197 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2197  in
               let uu____2198 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2198
               then
                 let uu____2201 =
                   let uu____2202 =
                     let uu____2209 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2209, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2202  in
                 mk1 uu____2201
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2214) ->
          let uu____2239 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2239 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2255 = FStar_Options.print_implicits ()  in
                 if uu____2255 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2293  ->
                         match uu____2293 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2333 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2333 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2343 = FStar_Options.print_implicits ()  in
                 if uu____2343 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2354 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2354 FStar_List.rev  in
               let rec aux body3 uu___2_2379 =
                 match uu___2_2379 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2395 =
            let uu____2400 =
              let uu____2401 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2401]  in
            FStar_Syntax_Subst.open_term uu____2400 phi  in
          (match uu____2395 with
           | (x1,phi1) ->
               let b =
                 let uu____2423 =
                   let uu____2426 = FStar_List.hd x1  in
                   resugar_binder' env uu____2426 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2423  in
               let uu____2433 =
                 let uu____2434 =
                   let uu____2439 = resugar_term' env phi1  in
                   (b, uu____2439)  in
                 FStar_Parser_AST.Refine uu____2434  in
               mk1 uu____2433)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2441;
             FStar_Syntax_Syntax.vars = uu____2442;_},(e,uu____2444)::[])
          when
          (let uu____2485 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2485) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2534 =
            match uu___3_2534 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2604 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2690,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2691))::tl1 ->
                  drop_implicits tl1
              | uu____2710 -> args2  in
            let uu____2719 = drop_implicits args1  in
            match uu____2719 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2751::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2781 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2881  ->
                   match uu____2881 with
                   | (e2,qual) ->
                       let uu____2898 = resugar_term' env e2  in
                       let uu____2899 = resugar_imp env qual  in
                       (uu____2898, uu____2899)) args1
               in
            let uu____2900 = resugar_term' env e1  in
            match uu____2900 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd1,previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd1, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc  ->
                     fun uu____2937  ->
                       match uu____2937 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2953 = FStar_Options.print_implicits ()  in
            if uu____2953 then args else filter_imp args  in
          let uu____2968 = resugar_term_as_op e  in
          (match uu____2968 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2981) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____3006  ->
                        match uu____3006 with
                        | (x,uu____3018) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____3027 =
                                   let uu____3028 =
                                     let uu____3029 =
                                       let uu____3036 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3036, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____3029  in
                                   mk1 uu____3028  in
                                 FStar_Pervasives_Native.Some uu____3027))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3040) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____3066)::[] -> b
                 | uu____3083 -> failwith "wrong arguments to dtuple"  in
               let uu____3093 =
                 let uu____3094 = FStar_Syntax_Subst.compress body  in
                 uu____3094.FStar_Syntax_Syntax.n  in
               (match uu____3093 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3099) ->
                    let uu____3124 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3124 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3134 = FStar_Options.print_implicits ()
                              in
                           if uu____3134 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3151 =
                           let uu____3152 =
                             let uu____3163 =
                               FStar_List.map
                                 (fun _3174  -> FStar_Util.Inl _3174) xs3
                                in
                             (uu____3163, body3)  in
                           FStar_Parser_AST.Sum uu____3152  in
                         mk1 uu____3151)
                | uu____3181 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3204  ->
                              match uu____3204 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3222) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3231) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3240 = FStar_List.hd args1  in
               (match uu____3240 with
                | (t1,uu____3254) ->
                    let uu____3259 =
                      let uu____3260 = FStar_Syntax_Subst.compress t1  in
                      uu____3260.FStar_Syntax_Syntax.n  in
                    (match uu____3259 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3267 =
                           let uu____3268 =
                             let uu____3273 = resugar_term' env t1  in
                             (uu____3273, f)  in
                           FStar_Parser_AST.Project uu____3268  in
                         mk1 uu____3267
                     | uu____3274 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3275) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___426_3302  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3312 =
                           match new_args with
                           | (a1,uu____3322)::(a2,uu____3324)::[] -> (a1, a2)
                           | uu____3351 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3312 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3373 =
                                  let uu____3374 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3374.FStar_Syntax_Syntax.n  in
                                match uu____3373 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3379) ->
                                    let uu____3404 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3404 with | (x1,e2) -> e2)
                                | uu____3411 ->
                                    let uu____3412 =
                                      let uu____3414 =
                                        let uu____3416 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3416
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3414
                                       in
                                    failwith uu____3412
                                 in
                              let body1 =
                                let uu____3419 = decomp body  in
                                resugar_term' env uu____3419  in
                              let handler1 =
                                let uu____3421 = decomp handler  in
                                resugar_term' env uu____3421  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3429,uu____3430,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3462,uu____3463,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3500 =
                                      let uu____3501 =
                                        let uu____3510 = resugar_body t11  in
                                        (uu____3510, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3501
                                       in
                                    mk1 uu____3500
                                | uu____3513 ->
                                    failwith
                                      "unexpected body format to try_with"
                                 in
                              let e1 = resugar_body body1  in
                              let rec resugar_branches t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match (e2,branches) ->
                                    branches
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    resugar_branches t11
                                | uu____3571 -> []  in
                              let branches = resugar_branches handler1  in
                              mk1 (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3604 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3605) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3614) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3637) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3702,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3734,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3765 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3778 =
                   let uu____3779 = FStar_Syntax_Subst.compress body  in
                   uu____3779.FStar_Syntax_Syntax.n  in
                 match uu____3778 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3784) ->
                     let uu____3809 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3809 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3819 = FStar_Options.print_implicits ()
                               in
                            if uu____3819 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3835 =
                            let uu____3844 =
                              let uu____3845 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3845.FStar_Syntax_Syntax.n  in
                            match uu____3844 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3863 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3880,pats) ->
                                      let uu____3914 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3958  ->
                                                     match uu____3958 with
                                                     | (e2,uu____3966) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3914, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3982 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3982)
                                  | uu____3991 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3863 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4023 ->
                                let uu____4024 = resugar_term' env body2  in
                                ([], uu____4024)
                             in
                          (match uu____3835 with
                           | (pats,body3) ->
                               let uu____4041 = uncurry xs3 pats body3  in
                               (match uu____4041 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4072 =
                                        let uu____4073 =
                                          let uu____4092 =
                                            let uu____4103 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4103, pats1)  in
                                          (xs4, uu____4092, body4)  in
                                        FStar_Parser_AST.QForall uu____4073
                                         in
                                      mk1 uu____4072
                                    else
                                      (let uu____4126 =
                                         let uu____4127 =
                                           let uu____4146 =
                                             let uu____4157 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4157, pats1)  in
                                           (xs4, uu____4146, body4)  in
                                         FStar_Parser_AST.QExists uu____4127
                                          in
                                       mk1 uu____4126))))
                 | uu____4178 ->
                     if op = "forall"
                     then
                       let uu____4182 =
                         let uu____4183 =
                           let uu____4202 = resugar_term' env body  in
                           ([], ([], []), uu____4202)  in
                         FStar_Parser_AST.QForall uu____4183  in
                       mk1 uu____4182
                     else
                       (let uu____4225 =
                          let uu____4226 =
                            let uu____4245 = resugar_term' env body  in
                            ([], ([], []), uu____4245)  in
                          FStar_Parser_AST.QExists uu____4226  in
                        mk1 uu____4225)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4284)::[] -> resugar_forall_body b
                  | uu____4301 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4313) ->
               let uu____4321 = FStar_List.hd args1  in
               (match uu____4321 with
                | (e1,uu____4335) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4407  ->
                         match uu____4407 with
                         | (e1,qual) ->
                             let uu____4424 = resugar_term' env e1  in
                             let uu____4425 = resugar_imp env qual  in
                             (uu____4424, uu____4425)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4441 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4441 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4489 =
                               let uu____4490 =
                                 let uu____4497 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4497)  in
                               FStar_Parser_AST.Op uu____4490  in
                             mk1 uu____4489  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4515  ->
                                  match uu____4515 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4534 =
                      let uu____4535 =
                        let uu____4542 =
                          let uu____4545 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4545
                           in
                        (op1, uu____4542)  in
                      FStar_Parser_AST.Op uu____4535  in
                    mk1 uu____4534
                | uu____4558 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4627 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4627 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4673 =
                   let uu____4686 =
                     let uu____4691 = resugar_pat' env pat1 branch_bv  in
                     let uu____4692 = resugar_term' env e  in
                     (uu____4691, uu____4692)  in
                   (FStar_Pervasives_Native.None, uu____4686)  in
                 [uu____4673]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4744,t1)::(pat2,uu____4747,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4843 =
            let uu____4844 =
              let uu____4851 = resugar_term' env e  in
              let uu____4852 = resugar_term' env t1  in
              let uu____4853 = resugar_term' env t2  in
              (uu____4851, uu____4852, uu____4853)  in
            FStar_Parser_AST.If uu____4844  in
          mk1 uu____4843
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4919 =
            match uu____4919 with
            | (pat,wopt,b) ->
                let uu____4961 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4961 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5013 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5013
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5017 =
            let uu____5018 =
              let uu____5033 = resugar_term' env e  in
              let uu____5034 = FStar_List.map resugar_branch branches  in
              (uu____5033, uu____5034)  in
            FStar_Parser_AST.Match uu____5018  in
          mk1 uu____5017
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5080) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5149 =
            let uu____5150 =
              let uu____5159 = resugar_term' env e  in
              (uu____5159, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5150  in
          mk1 uu____5149
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5188 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5188 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5242 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5242
                    in
                 let uu____5249 =
                   let uu____5254 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5254
                    in
                 match uu____5249 with
                 | (univs1,td) ->
                     let uu____5274 =
                       let uu____5281 =
                         let uu____5282 = FStar_Syntax_Subst.compress td  in
                         uu____5282.FStar_Syntax_Syntax.n  in
                       match uu____5281 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5291,(t1,uu____5293)::(d,uu____5295)::[])
                           -> (t1, d)
                       | uu____5352 -> failwith "wrong let binding format"
                        in
                     (match uu____5274 with
                      | (typ,def) ->
                          let uu____5383 =
                            let uu____5399 =
                              let uu____5400 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5400.FStar_Syntax_Syntax.n  in
                            match uu____5399 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5420) ->
                                let uu____5445 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5445 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5476 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5476
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5499 -> ([], def, false)  in
                          (match uu____5383 with
                           | (binders,term,is_pat_app) ->
                               let uu____5554 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5565 =
                                       let uu____5566 =
                                         let uu____5567 =
                                           let uu____5574 =
                                             bv_as_unique_ident bv  in
                                           (uu____5574,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5567
                                          in
                                       mk_pat uu____5566  in
                                     (uu____5565, term)
                                  in
                               (match uu____5554 with
                                | (pat,term1) ->
                                    let uu____5596 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5639  ->
                                                  match uu____5639 with
                                                  | (bv,q) ->
                                                      let uu____5654 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5654
                                                        (fun q1  ->
                                                           let uu____5666 =
                                                             let uu____5667 =
                                                               let uu____5674
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5674,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5667
                                                              in
                                                           mk_pat uu____5666)))
                                           in
                                        let uu____5677 =
                                          let uu____5682 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5682)
                                           in
                                        let uu____5685 =
                                          universe_to_string univs1  in
                                        (uu____5677, uu____5685)
                                      else
                                        (let uu____5694 =
                                           let uu____5699 =
                                             resugar_term' env term1  in
                                           (pat, uu____5699)  in
                                         let uu____5700 =
                                           universe_to_string univs1  in
                                         (uu____5694, uu____5700))
                                       in
                                    (attrs_opt, uu____5596))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5806 =
                   match uu____5806 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5866 =
                         let uu____5868 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5868  in
                       if uu____5866
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs1 (FStar_Pervasives_Native.snd pb))))
                    in
                 FStar_List.map f r  in
               let body2 = resugar_term' env body1  in
               mk1
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5949) ->
          let s =
            let uu____5968 =
              let uu____5970 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5970 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5968  in
          let uu____5975 = mk1 FStar_Parser_AST.Wild  in label s uu____5975
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5983 =
            let uu____5984 =
              let uu____5989 = resugar_term' env tm  in (uu____5989, qi1)  in
            FStar_Parser_AST.Quote uu____5984  in
          mk1 uu____5983
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_6001 =
            match uu___4_6001 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6009,(uu____6010,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6071 =
                        let uu____6072 =
                          let uu____6081 = resugar_seq t11  in
                          (uu____6081, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6072  in
                      mk1 uu____6071
                  | uu____6084 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6085,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6149  ->
                         match uu____6149 with
                         | (x,uu____6157) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6162 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6173,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6179,uu____6180,t1)
               -> resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun c  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____6220 = FStar_Options.print_universes ()  in
               if uu____6220
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
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
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____6284 = FStar_Options.print_universes ()  in
               if uu____6284
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
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
            let uu____6328 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6328, FStar_Parser_AST.Nothing)  in
          let uu____6329 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6329
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6352 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6352
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6437 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6437, (FStar_Pervasives_Native.snd post))  in
                    let uu____6448 =
                      let uu____6457 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6457 then [] else [pre]  in
                    let uu____6492 =
                      let uu____6501 =
                        let uu____6510 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6510 then [] else [pats]  in
                      FStar_List.append [post1] uu____6501  in
                    FStar_List.append uu____6448 uu____6492
                | uu____6569 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6603  ->
                   match uu____6603 with
                   | (e,uu____6615) ->
                       let uu____6620 = resugar_term' env e  in
                       (uu____6620, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6645 =
              match uu___5_6645 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6678 = resugar_term' env e  in
                         (uu____6678, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6683 -> aux l tl1)
               in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
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
  fun env  ->
    fun b  ->
      fun r  ->
        let uu____6730 = b  in
        match uu____6730 with
        | (x,aq) ->
            let uu____6739 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6739
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6753 =
                       let uu____6754 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6754  in
                     FStar_Parser_AST.mk_binder uu____6753 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6755 ->
                     let uu____6756 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6756
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6761 =
                          let uu____6762 =
                            let uu____6767 = bv_as_unique_ident x  in
                            (uu____6767, e)  in
                          FStar_Parser_AST.Annotated uu____6762  in
                        FStar_Parser_AST.mk_binder uu____6761 r
                          FStar_Parser_AST.Type_level imp))

and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun v1  ->
      fun aqual  ->
        fun body_bv  ->
          fun typ_opt  ->
            let mk1 a =
              let uu____6787 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6787  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6791 =
                if used
                then
                  let uu____6793 =
                    let uu____6800 = bv_as_unique_ident v1  in
                    (uu____6800, aqual)  in
                  FStar_Parser_AST.PatVar uu____6793
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6791  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6807;
                  FStar_Syntax_Syntax.vars = uu____6808;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6818 = FStar_Options.print_bound_var_types ()  in
                if uu____6818
                then
                  let uu____6821 =
                    let uu____6822 =
                      let uu____6833 =
                        let uu____6840 = resugar_term' env typ  in
                        (uu____6840, FStar_Pervasives_Native.None)  in
                      (pat, uu____6833)  in
                    FStar_Parser_AST.PatAscribed uu____6822  in
                  mk1 uu____6821
                else pat

and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____6861 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6861
            (fun aqual  ->
               let uu____6873 =
                 let uu____6878 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6889  -> FStar_Pervasives_Native.Some _6889)
                   uu____6878
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6873)

and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun p  ->
      fun branch_bv  ->
        let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b  ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None)
           in
        let may_drop_implicits args =
          (let uu____6951 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6951) &&
            (let uu____6954 =
               FStar_List.existsML
                 (fun uu____6967  ->
                    match uu____6967 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6989)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6994 -> false
                          | uu____6996 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6954)
           in
        let resugar_plain_pat_cons' fv args =
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args))
           in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____7064 = may_drop_implicits args  in
            if uu____7064 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7089  ->
                 match uu____7089 with
                 | (p1,b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1
             in
          resugar_plain_pat_cons' fv args2
        
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk1 (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
              mk1
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____7144 =
                  let uu____7146 =
                    let uu____7148 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7148  in
                  Prims.op_Negation uu____7146  in
                if uu____7144
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk1 (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____7192 = filter_pattern_imp args  in
              (match uu____7192 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7242 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7242 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7261 =
                       let uu____7267 =
                         let uu____7269 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7269
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7267)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7261);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7322  ->
                        match uu____7322 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7339 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7339)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7347;
                 FStar_Syntax_Syntax.fv_delta = uu____7348;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7377 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7377 FStar_List.rev  in
              let args1 =
                let uu____7393 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7413  ->
                          match uu____7413 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7393 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7491 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7491
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7514 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7514
                 in
              let args2 =
                let uu____7532 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7532 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7576 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7576 with
               | FStar_Pervasives_Native.Some (op,uu____7588) ->
                   let uu____7605 =
                     let uu____7606 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7606  in
                   mk1 uu____7605
               | FStar_Pervasives_Native.None  ->
                   let uu____7616 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7616 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7621 ->
              let uu____7622 =
                let uu____7623 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7623  in
              mk1 uu____7622
          | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term)
         in aux p FStar_Pervasives_Native.None

and (resugar_arg_qual :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun env  ->
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
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____7663 =
            let uu____7666 =
              let uu____7667 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7667  in
            FStar_Pervasives_Native.Some uu____7666  in
          FStar_Pervasives_Native.Some uu____7663

and (resugar_imp :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.imp)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> FStar_Parser_AST.Hash
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____7679 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7679

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7687  ->
    match uu___6_7687 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  -> FStar_Pervasives_Native.None
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
    | FStar_Syntax_Syntax.Logic  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____7694 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7695 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7696 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7701 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7710 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7719 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7725  ->
    match uu___7_7725 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions  -> FStar_Parser_AST.PopOptions
    | FStar_Syntax_Syntax.RestartSolver  -> FStar_Parser_AST.RestartSolver
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon))
  =
  fun env  ->
    fun datacon_ses  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid,uvs,bs,t,uu____7768,datacons) ->
            let uu____7778 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7806,uu____7807,uu____7808,inductive_lid,uu____7810,uu____7811)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7818 -> failwith "unexpected"))
               in
            (match uu____7778 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7839 = FStar_Options.print_implicits ()  in
                   if uu____7839 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7856 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7863  ->
                             match uu___8_7863 with
                             | FStar_Syntax_Syntax.RecordType uu____7865 ->
                                 true
                             | uu____7875 -> false))
                      in
                   if uu____7856
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7913,univs1,term,uu____7916,num,uu____7918)
                           ->
                           let uu____7925 =
                             let uu____7926 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7926.FStar_Syntax_Syntax.n  in
                           (match uu____7925 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7936)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7993  ->
                                          match uu____7993 with
                                          | (b,qual) ->
                                              let uu____8010 =
                                                bv_as_unique_ident b  in
                                              let uu____8011 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8010, uu____8011)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8016 -> failwith "unexpected")
                       | uu____8024 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     FStar_Parser_AST.TyconRecord
                       ((tylid.FStar_Ident.ident), bs2,
                         FStar_Pervasives_Native.None, fields)
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs1,term,uu____8119,num,uu____8121) ->
                            let c =
                              let uu____8138 =
                                let uu____8141 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8141  in
                              ((l.FStar_Ident.ident), uu____8138, false)  in
                            c :: constructors
                        | uu____8155 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8215 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
  
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____8241 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8241;
          FStar_Parser_AST.attrs = []
        }
  
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun name  ->
      fun ts  ->
        let uu____8271 = ts  in
        match uu____8271 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8284 =
              let uu____8285 =
                let uu____8296 =
                  let uu____8299 =
                    let uu____8300 =
                      let uu____8313 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____8313)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____8300  in
                  [uu____8299]  in
                (false, false, uu____8296)  in
              FStar_Parser_AST.Tycon uu____8285  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8284
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tscheme" ts 
let (resugar_wp_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.wp_eff_combinators ->
        FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun for_free  ->
      fun combs  ->
        let resugar_opt name tsopt =
          match tsopt with
          | FStar_Pervasives_Native.Some ts ->
              let uu____8378 = resugar_tscheme'' env name ts  in [uu____8378]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8396 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8398 =
             let uu____8401 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8403 =
               let uu____8406 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8408 =
                 let uu____8411 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8413 =
                   let uu____8416 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8418 =
                     let uu____8421 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8423 =
                       let uu____8426 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8426 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8421 :: uu____8423  in
                   uu____8416 :: uu____8418  in
                 uu____8411 :: uu____8413  in
               uu____8406 :: uu____8408  in
             uu____8401 :: uu____8403  in
           uu____8396 :: uu____8398)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8456 =
        match uu____8456 with
        | (ts,uu____8463) -> resugar_tscheme'' env name ts  in
      let uu____8464 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8466 =
        let uu____8469 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8471 =
          let uu____8474 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8476 =
            let uu____8479 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8481 =
              let uu____8484 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8484]  in
            uu____8479 :: uu____8481  in
          uu____8474 :: uu____8476  in
        uu____8469 :: uu____8471  in
      uu____8464 :: uu____8466
  
let (resugar_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.eff_combinators -> FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      match combs with
      | FStar_Syntax_Syntax.Primitive_eff combs1 ->
          resugar_wp_eff_combinators env false combs1
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          resugar_wp_eff_combinators env true combs1
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          resugar_layered_eff_combinators env combs1
  
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let resugar_action d for_free =
            let action_params =
              FStar_Syntax_Subst.open_binders
                d.FStar_Syntax_Syntax.action_params
               in
            let uu____8545 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8545 with
            | (bs,action_defn) ->
                let uu____8552 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8552 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8562 = FStar_Options.print_implicits ()  in
                       if uu____8562
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8572 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8572 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8589 =
                           let uu____8600 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8600,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8589  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false, false,
                              [FStar_Parser_AST.TyconAbbrev
                                 (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                   action_params2,
                                   FStar_Pervasives_Native.None, t)]))
                     else
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false, false,
                              [FStar_Parser_AST.TyconAbbrev
                                 (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                   action_params2,
                                   FStar_Pervasives_Native.None,
                                   action_defn1)])))
             in
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident  in
          let uu____8644 =
            let uu____8649 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8649
             in
          match uu____8644 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8667 = FStar_Options.print_implicits ()  in
                if uu____8667 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8677 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8677 FStar_List.rev  in
              let eff_typ1 = resugar_term' env eff_typ  in
              let mandatory_members_decls =
                resugar_combinators env ed.FStar_Syntax_Syntax.combinators
                 in
              let actions =
                FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                  (FStar_List.map (fun a  -> resugar_action a false))
                 in
              let decls = FStar_List.append mandatory_members_decls actions
                 in
              mk_decl r q
                (FStar_Parser_AST.NewEffect
                   (FStar_Parser_AST.DefineEffect
                      (eff_name, eff_binders2, eff_typ1, decls)))
  
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8727) ->
          let uu____8736 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8759 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8777 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8785 -> false
                    | uu____8802 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8736 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8840 se1 =
                 match uu____8840 with
                 | (datacon_ses1,tycons) ->
                     let uu____8866 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8866 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8881 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8881 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8916 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____8916
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8927,uu____8928,uu____8929,uu____8930,uu____8931)
                              ->
                              let uu____8938 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8938
                          | uu____8941 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8945 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_group ses -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8955) ->
          let uu____8960 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_8968  ->
                    match uu___9_8968 with
                    | FStar_Syntax_Syntax.Projector (uu____8970,uu____8971)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8973 -> true
                    | uu____8975 -> false))
             in
          if uu____8960
          then FStar_Pervasives_Native.None
          else
            (let mk1 e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng
                in
             let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let =
               mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))  in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____9010) ->
                 let uu____9039 =
                   let uu____9040 =
                     let uu____9041 =
                       let uu____9052 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9052)  in
                     FStar_Parser_AST.TopLevelLet uu____9041  in
                   decl'_to_decl se uu____9040  in
                 FStar_Pervasives_Native.Some uu____9039
             | uu____9089 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9094,fml) ->
          let uu____9096 =
            let uu____9097 =
              let uu____9098 =
                let uu____9103 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9103)  in
              FStar_Parser_AST.Assume uu____9098  in
            decl'_to_decl se uu____9097  in
          FStar_Pervasives_Native.Some uu____9096
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9105 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9105
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9114,t) ->
                let uu____9124 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9124
            | uu____9125 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9133,t) ->
                let uu____9143 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9143
            | uu____9144 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9168 -> failwith "Should not happen hopefully"  in
          let uu____9178 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9178
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9188 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9188 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9200 = FStar_Options.print_implicits ()  in
                 if uu____9200 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9216 =
                 let uu____9217 =
                   let uu____9218 =
                     let uu____9229 =
                       let uu____9232 =
                         let uu____9233 =
                           let uu____9246 = resugar_comp' env c1  in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____9246)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____9233  in
                       [uu____9232]  in
                     (false, false, uu____9229)  in
                   FStar_Parser_AST.Tycon uu____9218  in
                 decl'_to_decl se uu____9217  in
               FStar_Pervasives_Native.Some uu____9216)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9258 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9258
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9262 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9270  ->
                    match uu___10_9270 with
                    | FStar_Syntax_Syntax.Projector (uu____9272,uu____9273)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9275 -> true
                    | uu____9277 -> false))
             in
          if uu____9262
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9285 =
                 (let uu____9289 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9289) || (FStar_List.isEmpty uvs)
                  in
               if uu____9285
               then resugar_term' env t
               else
                 (let uu____9294 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9294 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9303 = resugar_term' env t1  in
                      label universes uu____9303)
                in
             let uu____9304 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9304)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9311 =
            let uu____9312 =
              let uu____9313 =
                let uu____9320 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9325 = resugar_term' env t  in
                (uu____9320, uu____9325)  in
              FStar_Parser_AST.Splice uu____9313  in
            decl'_to_decl se uu____9312  in
          FStar_Pervasives_Native.Some uu____9311
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9328 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9345 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9361 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n1,p,(uu____9365,t),uu____9367) ->
          let uu____9376 =
            let uu____9377 =
              let uu____9378 =
                let uu____9387 = resugar_term' env t  in
                (m, n1, p, uu____9387)  in
              FStar_Parser_AST.Polymonadic_bind uu____9378  in
            decl'_to_decl se uu____9377  in
          FStar_Pervasives_Native.Some uu____9376
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9411 = noenv resugar_term'  in uu____9411 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9429 = noenv resugar_sigelt'  in uu____9429 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9447 = noenv resugar_comp'  in uu____9447 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9470 = noenv resugar_pat'  in uu____9470 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9504 = noenv resugar_binder'  in uu____9504 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9529 = noenv resugar_tscheme'  in uu____9529 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9557 = noenv resugar_eff_decl'  in uu____9557 r q ed
  