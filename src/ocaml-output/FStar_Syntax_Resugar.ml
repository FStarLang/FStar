open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.of_int (100)) doc1
  
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
  
let rec (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env  -> fun u  -> fun r  -> resugar_universe u r

and (resugar_universe :
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
      | FStar_Syntax_Syntax.U_succ uu____342 ->
          let uu____343 = universe_to_int Prims.int_zero u  in
          (match uu____343 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____354 =
                      let uu____355 =
                        let uu____356 =
                          let uu____368 = FStar_Util.string_of_int n1  in
                          (uu____368, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____356  in
                      FStar_Parser_AST.Const uu____355  in
                    mk1 uu____354 r
                | uu____381 ->
                    let e1 =
                      let uu____383 =
                        let uu____384 =
                          let uu____385 =
                            let uu____397 = FStar_Util.string_of_int n1  in
                            (uu____397, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____385  in
                        FStar_Parser_AST.Const uu____384  in
                      mk1 uu____383 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____411 =
                      let uu____412 =
                        let uu____419 = FStar_Ident.id_of_text "+"  in
                        (uu____419, [e1; e2])  in
                      FStar_Parser_AST.Op uu____412  in
                    mk1 uu____411 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____427 ->
               let t =
                 let uu____431 =
                   let uu____432 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____432  in
                 mk1 uu____431 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____441 =
                        let uu____442 =
                          let uu____449 = resugar_universe x r  in
                          (acc, uu____449, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____442  in
                      mk1 uu____441 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____451 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____463 =
              let uu____469 =
                let uu____471 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____471  in
              (uu____469, r)  in
            FStar_Ident.mk_ident uu____463  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___1_509 =
      match uu___1_509 with
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
      | uu____837 -> FStar_Pervasives_Native.None  in
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
    | uu____977 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____995 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____995 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1013 ->
               let maybeop =
                 let uu____1021 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1087)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1021
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
      let uu____1419 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1419 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1489 ->
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
                (let uu____1591 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1591
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1627 =
      let uu____1628 = FStar_Syntax_Subst.compress t  in
      uu____1628.FStar_Syntax_Syntax.n  in
    match uu____1627 with
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
        let uu____1649 = string_to_op s  in
        (match uu____1649 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1689 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1706 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1723 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1734 -> true
    | uu____1736 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1757 ->
        let uu____1759 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1759
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1773 = may_shorten lid  in
      if uu____1773 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1918 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1918  in
      let uu____1921 =
        let uu____1922 = FStar_Syntax_Subst.compress t  in
        uu____1922.FStar_Syntax_Syntax.n  in
      match uu____1921 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1925 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1950 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1950
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1953 =
              let uu____1956 = bv_as_unique_ident x  in [uu____1956]  in
            FStar_Ident.lid_of_ids uu____1953  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1959 =
              let uu____1962 = bv_as_unique_ident x  in [uu____1962]  in
            FStar_Ident.lid_of_ids uu____1959  in
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
            let uu____1981 =
              let uu____1982 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1982  in
            mk1 uu____1981
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
               | uu____2006 -> failwith "wrong projector format")
            else
              (let uu____2013 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2013
               then
                 let uu____2016 =
                   let uu____2017 =
                     let uu____2018 =
                       let uu____2024 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2024)  in
                     FStar_Ident.mk_ident uu____2018  in
                   FStar_Parser_AST.Tvar uu____2017  in
                 mk1 uu____2016
               else
                 (let uu____2029 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2029
                  then
                    let uu____2032 =
                      let uu____2033 =
                        let uu____2034 =
                          let uu____2040 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2040)  in
                        FStar_Ident.mk_ident uu____2034  in
                      FStar_Parser_AST.Tvar uu____2033  in
                    mk1 uu____2032
                  else
                    (let uu____2045 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2049 =
                            let uu____2051 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2051  in
                          let uu____2054 = FStar_String.get s Prims.int_zero
                             in
                          uu____2049 <> uu____2054)
                        in
                     if uu____2045
                     then
                       let uu____2059 =
                         let uu____2060 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2060  in
                       mk1 uu____2059
                     else
                       (let uu____2063 =
                          let uu____2064 =
                            let uu____2075 = maybe_shorten_fv env fv  in
                            (uu____2075, [])  in
                          FStar_Parser_AST.Construct uu____2064  in
                        mk1 uu____2063))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2093 = FStar_Options.print_universes ()  in
          if uu____2093
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
                   let uu____2124 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2124  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2147 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2155 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2155
          then
            let uu____2158 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2158
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2163 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2184 -> ("Type", true)  in
          (match uu____2163 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2196 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2196  in
               let uu____2197 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2197
               then
                 let uu____2200 =
                   let uu____2201 =
                     let uu____2208 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2208, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2201  in
                 mk1 uu____2200
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2213) ->
          let uu____2238 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2238 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2254 = FStar_Options.print_implicits ()  in
                 if uu____2254 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2292  ->
                         match uu____2292 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2332 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2332 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2342 = FStar_Options.print_implicits ()  in
                 if uu____2342 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2353 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2353 FStar_List.rev  in
               let rec aux body3 uu___2_2378 =
                 match uu___2_2378 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2394 =
            let uu____2399 =
              let uu____2400 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2400]  in
            FStar_Syntax_Subst.open_term uu____2399 phi  in
          (match uu____2394 with
           | (x1,phi1) ->
               let b =
                 let uu____2422 =
                   let uu____2425 = FStar_List.hd x1  in
                   resugar_binder' env uu____2425 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2422  in
               let uu____2432 =
                 let uu____2433 =
                   let uu____2438 = resugar_term' env phi1  in
                   (b, uu____2438)  in
                 FStar_Parser_AST.Refine uu____2433  in
               mk1 uu____2432)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2440;
             FStar_Syntax_Syntax.vars = uu____2441;_},(e,uu____2443)::[])
          when
          (let uu____2484 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2484) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2533 =
            match uu___3_2533 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2603 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2689,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2690))::tl1 ->
                  drop_implicits tl1
              | uu____2709 -> args2  in
            let uu____2718 = drop_implicits args1  in
            match uu____2718 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2750::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2780 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2880  ->
                   match uu____2880 with
                   | (e2,qual) ->
                       let uu____2897 = resugar_term' env e2  in
                       let uu____2898 = resugar_imp env qual  in
                       (uu____2897, uu____2898)) args1
               in
            let uu____2899 = resugar_term' env e1  in
            match uu____2899 with
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
                     fun uu____2936  ->
                       match uu____2936 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2952 = FStar_Options.print_implicits ()  in
            if uu____2952 then args else filter_imp args  in
          let uu____2967 = resugar_term_as_op e  in
          (match uu____2967 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2980) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____3005  ->
                        match uu____3005 with
                        | (x,uu____3017) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____3026 =
                                   let uu____3027 =
                                     let uu____3028 =
                                       let uu____3035 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3035, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____3028  in
                                   mk1 uu____3027  in
                                 FStar_Pervasives_Native.Some uu____3026))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3039) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____3065)::[] -> b
                 | uu____3082 -> failwith "wrong arguments to dtuple"  in
               let uu____3092 =
                 let uu____3093 = FStar_Syntax_Subst.compress body  in
                 uu____3093.FStar_Syntax_Syntax.n  in
               (match uu____3092 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3098) ->
                    let uu____3123 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3123 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3133 = FStar_Options.print_implicits ()
                              in
                           if uu____3133 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3150 =
                           let uu____3151 =
                             let uu____3162 =
                               FStar_List.map
                                 (fun _3173  -> FStar_Util.Inl _3173) xs3
                                in
                             (uu____3162, body3)  in
                           FStar_Parser_AST.Sum uu____3151  in
                         mk1 uu____3150)
                | uu____3180 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3203  ->
                              match uu____3203 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3221) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3230) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3239 = FStar_List.hd args1  in
               (match uu____3239 with
                | (t1,uu____3253) ->
                    let uu____3258 =
                      let uu____3259 = FStar_Syntax_Subst.compress t1  in
                      uu____3259.FStar_Syntax_Syntax.n  in
                    (match uu____3258 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3266 =
                           let uu____3267 =
                             let uu____3272 = resugar_term' env t1  in
                             (uu____3272, f)  in
                           FStar_Parser_AST.Project uu____3267  in
                         mk1 uu____3266
                     | uu____3273 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3274) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___426_3301  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3311 =
                           match new_args with
                           | (a1,uu____3321)::(a2,uu____3323)::[] -> (a1, a2)
                           | uu____3350 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3311 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3372 =
                                  let uu____3373 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3373.FStar_Syntax_Syntax.n  in
                                match uu____3372 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3378) ->
                                    let uu____3403 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3403 with | (x1,e2) -> e2)
                                | uu____3410 ->
                                    let uu____3411 =
                                      let uu____3413 =
                                        let uu____3415 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3415
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3413
                                       in
                                    failwith uu____3411
                                 in
                              let body1 =
                                let uu____3418 = decomp body  in
                                resugar_term' env uu____3418  in
                              let handler1 =
                                let uu____3420 = decomp handler  in
                                resugar_term' env uu____3420  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3428,uu____3429,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3461,uu____3462,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3499 =
                                      let uu____3500 =
                                        let uu____3509 = resugar_body t11  in
                                        (uu____3509, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3500
                                       in
                                    mk1 uu____3499
                                | uu____3512 ->
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
                                | uu____3570 -> []  in
                              let branches = resugar_branches handler1  in
                              mk1 (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3603 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3604) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3613) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3634) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,(uu____3699,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,(uu____3731,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3762 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3775 =
                   let uu____3776 = FStar_Syntax_Subst.compress body  in
                   uu____3776.FStar_Syntax_Syntax.n  in
                 match uu____3775 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3781) ->
                     let uu____3806 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3806 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3816 = FStar_Options.print_implicits ()
                               in
                            if uu____3816 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3832 =
                            let uu____3841 =
                              let uu____3842 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3842.FStar_Syntax_Syntax.n  in
                            match uu____3841 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3860 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3877,pats) ->
                                      let uu____3911 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3955  ->
                                                     match uu____3955 with
                                                     | (e2,uu____3963) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3911, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3979 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3979)
                                  | uu____3988 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3860 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4020 ->
                                let uu____4021 = resugar_term' env body2  in
                                ([], uu____4021)
                             in
                          (match uu____3832 with
                           | (pats,body3) ->
                               let uu____4038 = uncurry xs3 pats body3  in
                               (match uu____4038 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      let uu____4076 =
                                        let uu____4077 =
                                          let uu____4096 =
                                            let uu____4107 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs5 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4107, pats1)  in
                                          (xs5, uu____4096, body4)  in
                                        FStar_Parser_AST.QForall uu____4077
                                         in
                                      mk1 uu____4076
                                    else
                                      (let uu____4130 =
                                         let uu____4131 =
                                           let uu____4150 =
                                             let uu____4161 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs5
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4161, pats1)  in
                                           (xs5, uu____4150, body4)  in
                                         FStar_Parser_AST.QExists uu____4131
                                          in
                                       mk1 uu____4130))))
                 | uu____4182 ->
                     if op = "forall"
                     then
                       let uu____4186 =
                         let uu____4187 =
                           let uu____4206 = resugar_term' env body  in
                           ([], ([], []), uu____4206)  in
                         FStar_Parser_AST.QForall uu____4187  in
                       mk1 uu____4186
                     else
                       (let uu____4229 =
                          let uu____4230 =
                            let uu____4249 = resugar_term' env body  in
                            ([], ([], []), uu____4249)  in
                          FStar_Parser_AST.QExists uu____4230  in
                        mk1 uu____4229)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4288)::[] -> resugar b
                  | uu____4305 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4317) ->
               let uu____4325 = FStar_List.hd args1  in
               (match uu____4325 with
                | (e1,uu____4339) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4411  ->
                         match uu____4411 with
                         | (e1,qual) ->
                             let uu____4428 = resugar_term' env e1  in
                             let uu____4429 = resugar_imp env qual  in
                             (uu____4428, uu____4429)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4445 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4445 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4493 =
                               let uu____4494 =
                                 let uu____4501 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4501)  in
                               FStar_Parser_AST.Op uu____4494  in
                             mk1 uu____4493  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4519  ->
                                  match uu____4519 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4538 =
                      let uu____4539 =
                        let uu____4546 =
                          let uu____4549 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4549
                           in
                        (op1, uu____4546)  in
                      FStar_Parser_AST.Op uu____4539  in
                    mk1 uu____4538
                | uu____4562 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4631 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4631 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4677 =
                   let uu____4690 =
                     let uu____4695 = resugar_pat' env pat1 branch_bv  in
                     let uu____4696 = resugar_term' env e  in
                     (uu____4695, uu____4696)  in
                   (FStar_Pervasives_Native.None, uu____4690)  in
                 [uu____4677]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4748,t1)::(pat2,uu____4751,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4847 =
            let uu____4848 =
              let uu____4855 = resugar_term' env e  in
              let uu____4856 = resugar_term' env t1  in
              let uu____4857 = resugar_term' env t2  in
              (uu____4855, uu____4856, uu____4857)  in
            FStar_Parser_AST.If uu____4848  in
          mk1 uu____4847
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4923 =
            match uu____4923 with
            | (pat,wopt,b) ->
                let uu____4965 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4965 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5017 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5017
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5021 =
            let uu____5022 =
              let uu____5037 = resugar_term' env e  in
              let uu____5038 = FStar_List.map resugar_branch branches  in
              (uu____5037, uu____5038)  in
            FStar_Parser_AST.Match uu____5022  in
          mk1 uu____5021
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5084) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5153 =
            let uu____5154 =
              let uu____5163 = resugar_term' env e  in
              (uu____5163, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5154  in
          mk1 uu____5153
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5192 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5192 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5246 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5246
                    in
                 let uu____5253 =
                   let uu____5258 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5258
                    in
                 match uu____5253 with
                 | (univs1,td) ->
                     let uu____5278 =
                       let uu____5285 =
                         let uu____5286 = FStar_Syntax_Subst.compress td  in
                         uu____5286.FStar_Syntax_Syntax.n  in
                       match uu____5285 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5295,(t1,uu____5297)::(d,uu____5299)::[])
                           -> (t1, d)
                       | uu____5356 -> failwith "wrong let binding format"
                        in
                     (match uu____5278 with
                      | (typ,def) ->
                          let uu____5387 =
                            let uu____5403 =
                              let uu____5404 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5404.FStar_Syntax_Syntax.n  in
                            match uu____5403 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5424) ->
                                let uu____5449 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5449 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5480 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5480
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5503 -> ([], def, false)  in
                          (match uu____5387 with
                           | (binders,term,is_pat_app) ->
                               let uu____5558 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5569 =
                                       let uu____5570 =
                                         let uu____5571 =
                                           let uu____5578 =
                                             bv_as_unique_ident bv  in
                                           (uu____5578,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5571
                                          in
                                       mk_pat uu____5570  in
                                     (uu____5569, term)
                                  in
                               (match uu____5558 with
                                | (pat,term1) ->
                                    let uu____5600 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5643  ->
                                                  match uu____5643 with
                                                  | (bv,q) ->
                                                      let uu____5658 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5658
                                                        (fun q1  ->
                                                           let uu____5670 =
                                                             let uu____5671 =
                                                               let uu____5678
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5678,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5671
                                                              in
                                                           mk_pat uu____5670)))
                                           in
                                        let uu____5681 =
                                          let uu____5686 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5686)
                                           in
                                        let uu____5689 =
                                          universe_to_string univs1  in
                                        (uu____5681, uu____5689)
                                      else
                                        (let uu____5698 =
                                           let uu____5703 =
                                             resugar_term' env term1  in
                                           (pat, uu____5703)  in
                                         let uu____5704 =
                                           universe_to_string univs1  in
                                         (uu____5698, uu____5704))
                                       in
                                    (attrs_opt, uu____5600))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5810 =
                   match uu____5810 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5870 =
                         let uu____5872 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5872  in
                       if uu____5870
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5953) ->
          let s =
            let uu____5972 =
              let uu____5974 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5974 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5972  in
          let uu____5979 = mk1 FStar_Parser_AST.Wild  in label s uu____5979
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5987 =
            let uu____5988 =
              let uu____5993 = resugar_term' env tm  in (uu____5993, qi1)  in
            FStar_Parser_AST.Quote uu____5988  in
          mk1 uu____5987
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_6005 =
            match uu___4_6005 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6013,(uu____6014,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6075 =
                        let uu____6076 =
                          let uu____6085 = resugar_seq t11  in
                          (uu____6085, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6076  in
                      mk1 uu____6075
                  | uu____6088 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6089,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6153  ->
                         match uu____6153 with
                         | (x,uu____6161) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6166 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____6184,t1) ->
               resugar_term' env e)
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
               let uu____6224 = FStar_Options.print_universes ()  in
               if uu____6224
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
               let uu____6288 = FStar_Options.print_universes ()  in
               if uu____6288
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
            let uu____6332 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6332, FStar_Parser_AST.Nothing)  in
          let uu____6333 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6333
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6356 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6356
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6441 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6441, (FStar_Pervasives_Native.snd post))  in
                    let uu____6452 =
                      let uu____6461 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6461 then [] else [pre]  in
                    let uu____6496 =
                      let uu____6505 =
                        let uu____6514 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6514 then [] else [pats]  in
                      FStar_List.append [post1] uu____6505  in
                    FStar_List.append uu____6452 uu____6496
                | uu____6573 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6607  ->
                   match uu____6607 with
                   | (e,uu____6619) ->
                       let uu____6624 = resugar_term' env e  in
                       (uu____6624, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6649 =
              match uu___5_6649 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6682 = resugar_term' env e  in
                         (uu____6682, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6687 -> aux l tl1)
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
        let uu____6734 = b  in
        match uu____6734 with
        | (x,aq) ->
            let uu____6743 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6743
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6757 =
                       let uu____6758 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6758  in
                     FStar_Parser_AST.mk_binder uu____6757 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6759 ->
                     let uu____6760 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6760
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6765 =
                          let uu____6766 =
                            let uu____6771 = bv_as_unique_ident x  in
                            (uu____6771, e)  in
                          FStar_Parser_AST.Annotated uu____6766  in
                        FStar_Parser_AST.mk_binder uu____6765 r
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
              let uu____6791 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6791  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6795 =
                if used
                then
                  let uu____6797 =
                    let uu____6804 = bv_as_unique_ident v1  in
                    (uu____6804, aqual)  in
                  FStar_Parser_AST.PatVar uu____6797
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6795  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6811;
                  FStar_Syntax_Syntax.vars = uu____6812;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6822 = FStar_Options.print_bound_var_types ()  in
                if uu____6822
                then
                  let uu____6825 =
                    let uu____6826 =
                      let uu____6837 =
                        let uu____6844 = resugar_term' env typ  in
                        (uu____6844, FStar_Pervasives_Native.None)  in
                      (pat, uu____6837)  in
                    FStar_Parser_AST.PatAscribed uu____6826  in
                  mk1 uu____6825
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
          let uu____6865 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6865
            (fun aqual  ->
               let uu____6877 =
                 let uu____6882 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6893  -> FStar_Pervasives_Native.Some _6893)
                   uu____6882
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6877)

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
          (let uu____6955 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6955) &&
            (let uu____6958 =
               FStar_List.existsML
                 (fun uu____6971  ->
                    match uu____6971 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6993)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6998 -> false
                          | uu____7000 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6958)
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
            let uu____7068 = may_drop_implicits args  in
            if uu____7068 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7093  ->
                 match uu____7093 with
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
              ((let uu____7148 =
                  let uu____7150 =
                    let uu____7152 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7152  in
                  Prims.op_Negation uu____7150  in
                if uu____7148
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
              let uu____7196 = filter_pattern_imp args  in
              (match uu____7196 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7246 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7246 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7265 =
                       let uu____7271 =
                         let uu____7273 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7273
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7271)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7265);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7326  ->
                        match uu____7326 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7343 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7343)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7351;
                 FStar_Syntax_Syntax.fv_delta = uu____7352;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7381 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7381 FStar_List.rev  in
              let args1 =
                let uu____7397 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7417  ->
                          match uu____7417 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7397 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7495 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7495
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7518 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7518
                 in
              let args2 =
                let uu____7536 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7536 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7580 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7580 with
               | FStar_Pervasives_Native.Some (op,uu____7592) ->
                   let uu____7609 =
                     let uu____7610 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7610  in
                   mk1 uu____7609
               | FStar_Pervasives_Native.None  ->
                   let uu____7620 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7620 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7625 ->
              let uu____7626 =
                let uu____7627 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7627  in
              mk1 uu____7626
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
          let uu____7667 =
            let uu____7670 =
              let uu____7671 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7671  in
            FStar_Pervasives_Native.Some uu____7670  in
          FStar_Pervasives_Native.Some uu____7667

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
          let uu____7683 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7683

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7691  ->
    match uu___6_7691 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7698 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7699 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7700 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7705 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7714 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7723 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7729  ->
    match uu___7_7729 with
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
            (tylid,uvs,bs,t,uu____7772,datacons) ->
            let uu____7782 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7810,uu____7811,uu____7812,inductive_lid,uu____7814,uu____7815)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7822 -> failwith "unexpected"))
               in
            (match uu____7782 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7843 = FStar_Options.print_implicits ()  in
                   if uu____7843 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7860 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7867  ->
                             match uu___8_7867 with
                             | FStar_Syntax_Syntax.RecordType uu____7869 ->
                                 true
                             | uu____7879 -> false))
                      in
                   if uu____7860
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7933,univs1,term,uu____7936,num,uu____7938)
                           ->
                           let uu____7945 =
                             let uu____7946 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7946.FStar_Syntax_Syntax.n  in
                           (match uu____7945 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7960)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____8029  ->
                                          match uu____8029 with
                                          | (b,qual) ->
                                              let uu____8050 =
                                                bv_as_unique_ident b  in
                                              let uu____8051 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8050, uu____8051,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8062 -> failwith "unexpected")
                       | uu____8074 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____8205,num,uu____8207) ->
                            let c =
                              let uu____8228 =
                                let uu____8231 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8231  in
                              ((l.FStar_Ident.ident), uu____8228,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____8251 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8331 ->
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
        let uu____8357 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8357;
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
        let uu____8387 = ts  in
        match uu____8387 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8400 =
              let uu____8401 =
                let uu____8418 =
                  let uu____8427 =
                    let uu____8434 =
                      let uu____8435 =
                        let uu____8448 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8448)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8435  in
                    (uu____8434, FStar_Pervasives_Native.None)  in
                  [uu____8427]  in
                (false, false, uu____8418)  in
              FStar_Parser_AST.Tycon uu____8401  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8400
  
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
              let uu____8533 = resugar_tscheme'' env name ts  in [uu____8533]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8551 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8553 =
             let uu____8556 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8558 =
               let uu____8561 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8563 =
                 let uu____8566 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8568 =
                   let uu____8571 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8573 =
                     let uu____8576 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8578 =
                       let uu____8581 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8581 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8576 :: uu____8578  in
                   uu____8571 :: uu____8573  in
                 uu____8566 :: uu____8568  in
               uu____8561 :: uu____8563  in
             uu____8556 :: uu____8558  in
           uu____8551 :: uu____8553)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8611 =
        match uu____8611 with
        | (ts,uu____8618) -> resugar_tscheme'' env name ts  in
      let uu____8619 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8621 =
        let uu____8624 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8626 =
          let uu____8629 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8631 =
            let uu____8634 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8636 =
              let uu____8639 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8639]  in
            uu____8634 :: uu____8636  in
          uu____8629 :: uu____8631  in
        uu____8624 :: uu____8626  in
      uu____8619 :: uu____8621
  
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
            let uu____8700 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8700 with
            | (bs,action_defn) ->
                let uu____8707 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8707 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8717 = FStar_Options.print_implicits ()  in
                       if uu____8717
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8727 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8727 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8744 =
                           let uu____8755 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8755,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8744  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false, false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2,
                                     FStar_Pervasives_Native.None, t)),
                                 FStar_Pervasives_Native.None)]))
                     else
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false, false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2,
                                     FStar_Pervasives_Native.None,
                                     action_defn1)),
                                 FStar_Pervasives_Native.None)])))
             in
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident  in
          let uu____8839 =
            let uu____8844 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8844
             in
          match uu____8839 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8862 = FStar_Options.print_implicits ()  in
                if uu____8862 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8872 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8872 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8922) ->
          let uu____8931 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8954 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8972 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8980 -> false
                    | uu____8997 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8931 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____9035 se1 =
                 match uu____9035 with
                 | (datacon_ses1,tycons) ->
                     let uu____9061 = resugar_typ env datacon_ses1 se1  in
                     (match uu____9061 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____9076 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____9076 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____9111 =
                           let uu____9112 =
                             let uu____9113 =
                               let uu____9130 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____9130)  in
                             FStar_Parser_AST.Tycon uu____9113  in
                           decl'_to_decl se uu____9112  in
                         FStar_Pervasives_Native.Some uu____9111
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____9165,uu____9166,uu____9167,uu____9168,uu____9169)
                              ->
                              let uu____9176 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____9176
                          | uu____9179 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____9183 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9190) ->
          let uu____9195 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_9203  ->
                    match uu___9_9203 with
                    | FStar_Syntax_Syntax.Projector (uu____9205,uu____9206)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9208 -> true
                    | uu____9210 -> false))
             in
          if uu____9195
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9245) ->
                 let uu____9274 =
                   let uu____9275 =
                     let uu____9276 =
                       let uu____9287 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9287)  in
                     FStar_Parser_AST.TopLevelLet uu____9276  in
                   decl'_to_decl se uu____9275  in
                 FStar_Pervasives_Native.Some uu____9274
             | uu____9324 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9329,fml) ->
          let uu____9331 =
            let uu____9332 =
              let uu____9333 =
                let uu____9338 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9338)  in
              FStar_Parser_AST.Assume uu____9333  in
            decl'_to_decl se uu____9332  in
          FStar_Pervasives_Native.Some uu____9331
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9340 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9340
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9349,t) ->
                let uu____9359 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9359
            | uu____9360 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9368,t) ->
                let uu____9378 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9378
            | uu____9379 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9403 -> failwith "Should not happen hopefully"  in
          let uu____9413 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9413
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9423 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9423 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9435 = FStar_Options.print_implicits ()  in
                 if uu____9435 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9451 =
                 let uu____9452 =
                   let uu____9453 =
                     let uu____9470 =
                       let uu____9479 =
                         let uu____9486 =
                           let uu____9487 =
                             let uu____9500 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9500)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9487  in
                         (uu____9486, FStar_Pervasives_Native.None)  in
                       [uu____9479]  in
                     (false, false, uu____9470)  in
                   FStar_Parser_AST.Tycon uu____9453  in
                 decl'_to_decl se uu____9452  in
               FStar_Pervasives_Native.Some uu____9451)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9532 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9532
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9536 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9544  ->
                    match uu___10_9544 with
                    | FStar_Syntax_Syntax.Projector (uu____9546,uu____9547)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9549 -> true
                    | uu____9551 -> false))
             in
          if uu____9536
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9559 =
                 (let uu____9563 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9563) || (FStar_List.isEmpty uvs)
                  in
               if uu____9559
               then resugar_term' env t
               else
                 (let uu____9568 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9568 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9577 = resugar_term' env t1  in
                      label universes uu____9577)
                in
             let uu____9578 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9578)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9585 =
            let uu____9586 =
              let uu____9587 =
                let uu____9594 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9599 = resugar_term' env t  in
                (uu____9594, uu____9599)  in
              FStar_Parser_AST.Splice uu____9587  in
            decl'_to_decl se uu____9586  in
          FStar_Pervasives_Native.Some uu____9585
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9602 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9619 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9635 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9659 = noenv resugar_term'  in uu____9659 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9677 = noenv resugar_sigelt'  in uu____9677 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9695 = noenv resugar_comp'  in uu____9695 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9718 = noenv resugar_pat'  in uu____9718 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9752 = noenv resugar_binder'  in uu____9752 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9777 = noenv resugar_tscheme'  in uu____9777 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9805 = noenv resugar_eff_decl'  in uu____9805 r q ed
  