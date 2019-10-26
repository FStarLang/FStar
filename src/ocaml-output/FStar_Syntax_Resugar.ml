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
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____2017 =
                      let uu____2019 = FStar_String.get s Prims.int_zero  in
                      FStar_Char.uppercase uu____2019  in
                    let uu____2022 = FStar_String.get s Prims.int_zero  in
                    uu____2017 <> uu____2022)
                  in
               if uu____2013
               then
                 let uu____2027 =
                   let uu____2028 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____2028  in
                 mk1 uu____2027
               else
                 (let uu____2031 =
                    let uu____2032 =
                      let uu____2043 = maybe_shorten_fv env fv  in
                      (uu____2043, [])  in
                    FStar_Parser_AST.Construct uu____2032  in
                  mk1 uu____2031))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2061 = FStar_Options.print_universes ()  in
          if uu____2061
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
                   let uu____2092 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2092  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2115 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2123 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2123
          then
            let uu____2126 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2126
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2131 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2152 -> ("Type", true)  in
          (match uu____2131 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2164 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2164  in
               let uu____2165 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2165
               then
                 let uu____2168 =
                   let uu____2169 =
                     let uu____2176 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2176, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2169  in
                 mk1 uu____2168
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2181) ->
          let uu____2206 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2206 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2222 = FStar_Options.print_implicits ()  in
                 if uu____2222 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2260  ->
                         match uu____2260 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2300 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2300 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2310 = FStar_Options.print_implicits ()  in
                 if uu____2310 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2321 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2321 FStar_List.rev  in
               let rec aux body3 uu___2_2346 =
                 match uu___2_2346 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2362 =
            let uu____2367 =
              let uu____2368 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2368]  in
            FStar_Syntax_Subst.open_term uu____2367 phi  in
          (match uu____2362 with
           | (x1,phi1) ->
               let b =
                 let uu____2390 =
                   let uu____2393 = FStar_List.hd x1  in
                   resugar_binder' env uu____2393 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2390  in
               let uu____2400 =
                 let uu____2401 =
                   let uu____2406 = resugar_term' env phi1  in
                   (b, uu____2406)  in
                 FStar_Parser_AST.Refine uu____2401  in
               mk1 uu____2400)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2408;
             FStar_Syntax_Syntax.vars = uu____2409;_},(e,uu____2411)::[])
          when
          (let uu____2452 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2452) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2501 =
            match uu___3_2501 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2571 -> failwith "last of an empty list"  in
          let rec last_two uu___4_2610 =
            match uu___4_2610 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____2642::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2720::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2791  ->
                   match uu____2791 with
                   | (e2,qual) ->
                       let uu____2808 = resugar_term' env e2  in
                       let uu____2809 = resugar_imp env qual  in
                       (uu____2808, uu____2809)) args1
               in
            let uu____2810 = resugar_term' env e1  in
            match uu____2810 with
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
                     fun uu____2847  ->
                       match uu____2847 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2863 = FStar_Options.print_implicits ()  in
            if uu____2863 then args else filter_imp args  in
          let uu____2878 = resugar_term_as_op e  in
          (match uu____2878 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2891) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2916  ->
                        match uu____2916 with
                        | (x,uu____2928) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2937 =
                                   let uu____2938 =
                                     let uu____2939 =
                                       let uu____2946 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2946, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2939  in
                                   mk1 uu____2938  in
                                 FStar_Pervasives_Native.Some uu____2937))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2950) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2976)::[] -> b
                 | uu____2993 -> failwith "wrong arguments to dtuple"  in
               let uu____3003 =
                 let uu____3004 = FStar_Syntax_Subst.compress body  in
                 uu____3004.FStar_Syntax_Syntax.n  in
               (match uu____3003 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3009) ->
                    let uu____3034 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3034 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3044 = FStar_Options.print_implicits ()
                              in
                           if uu____3044 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3061 =
                           let uu____3062 =
                             let uu____3073 =
                               FStar_List.map
                                 (fun _3084  -> FStar_Util.Inl _3084) xs3
                                in
                             (uu____3073, body3)  in
                           FStar_Parser_AST.Sum uu____3062  in
                         mk1 uu____3061)
                | uu____3091 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3114  ->
                              match uu____3114 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3132) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3141) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3150 = FStar_List.hd args1  in
               (match uu____3150 with
                | (t1,uu____3164) ->
                    let uu____3169 =
                      let uu____3170 = FStar_Syntax_Subst.compress t1  in
                      uu____3170.FStar_Syntax_Syntax.n  in
                    (match uu____3169 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3177 =
                           let uu____3178 =
                             let uu____3183 = resugar_term' env t1  in
                             (uu____3183, f)  in
                           FStar_Parser_AST.Project uu____3178  in
                         mk1 uu____3177
                     | uu____3184 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3185) when
               (FStar_List.length args1) > Prims.int_one ->
               let new_args = last_two args1  in
               let uu____3209 =
                 match new_args with
                 | (a1,uu____3219)::(a2,uu____3221)::[] -> (a1, a2)
                 | uu____3248 -> failwith "wrong arguments to try_with"  in
               (match uu____3209 with
                | (body,handler) ->
                    let decomp term =
                      let uu____3270 =
                        let uu____3271 = FStar_Syntax_Subst.compress term  in
                        uu____3271.FStar_Syntax_Syntax.n  in
                      match uu____3270 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____3276) ->
                          let uu____3301 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____3301 with | (x1,e2) -> e2)
                      | uu____3308 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____3311 = decomp body  in
                      resugar_term' env uu____3311  in
                    let handler1 =
                      let uu____3313 = decomp handler  in
                      resugar_term' env uu____3313  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____3321,uu____3322,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____3354,uu____3355,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____3392 =
                            let uu____3393 =
                              let uu____3402 = resugar_body t11  in
                              (uu____3402, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____3393  in
                          mk1 uu____3392
                      | uu____3405 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____3463 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____3493) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3502) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3523) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,(uu____3588,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,(uu____3620,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3651 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3664 =
                   let uu____3665 = FStar_Syntax_Subst.compress body  in
                   uu____3665.FStar_Syntax_Syntax.n  in
                 match uu____3664 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3670) ->
                     let uu____3695 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3695 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3705 = FStar_Options.print_implicits ()
                               in
                            if uu____3705 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3721 =
                            let uu____3730 =
                              let uu____3731 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3731.FStar_Syntax_Syntax.n  in
                            match uu____3730 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3749 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3766,pats) ->
                                      let uu____3800 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3844  ->
                                                     match uu____3844 with
                                                     | (e2,uu____3852) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3800, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3868 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3868)
                                  | uu____3877 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3749 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3909 ->
                                let uu____3910 = resugar_term' env body2  in
                                ([], uu____3910)
                             in
                          (match uu____3721 with
                           | (pats,body3) ->
                               let uu____3927 = uncurry xs3 pats body3  in
                               (match uu____3927 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      let uu____3965 =
                                        let uu____3966 =
                                          let uu____3985 =
                                            let uu____3996 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs5 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____3996, pats1)  in
                                          (xs5, uu____3985, body4)  in
                                        FStar_Parser_AST.QForall uu____3966
                                         in
                                      mk1 uu____3965
                                    else
                                      (let uu____4019 =
                                         let uu____4020 =
                                           let uu____4039 =
                                             let uu____4050 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs5
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4050, pats1)  in
                                           (xs5, uu____4039, body4)  in
                                         FStar_Parser_AST.QExists uu____4020
                                          in
                                       mk1 uu____4019))))
                 | uu____4071 ->
                     if op = "forall"
                     then
                       let uu____4075 =
                         let uu____4076 =
                           let uu____4095 = resugar_term' env body  in
                           ([], ([], []), uu____4095)  in
                         FStar_Parser_AST.QForall uu____4076  in
                       mk1 uu____4075
                     else
                       (let uu____4118 =
                          let uu____4119 =
                            let uu____4138 = resugar_term' env body  in
                            ([], ([], []), uu____4138)  in
                          FStar_Parser_AST.QExists uu____4119  in
                        mk1 uu____4118)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4177)::[] -> resugar b
                  | uu____4194 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4206) ->
               let uu____4214 = FStar_List.hd args1  in
               (match uu____4214 with
                | (e1,uu____4228) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4300  ->
                         match uu____4300 with
                         | (e1,qual) ->
                             let uu____4317 = resugar_term' env e1  in
                             let uu____4318 = resugar_imp env qual  in
                             (uu____4317, uu____4318)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4334 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4334 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4382 =
                               let uu____4383 =
                                 let uu____4390 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4390)  in
                               FStar_Parser_AST.Op uu____4383  in
                             mk1 uu____4382  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4408  ->
                                  match uu____4408 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4427 =
                      let uu____4428 =
                        let uu____4435 =
                          let uu____4438 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4438
                           in
                        (op1, uu____4435)  in
                      FStar_Parser_AST.Op uu____4428  in
                    mk1 uu____4427
                | uu____4451 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4520 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4520 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4566 =
                   let uu____4579 =
                     let uu____4584 = resugar_pat' env pat1 branch_bv  in
                     let uu____4585 = resugar_term' env e  in
                     (uu____4584, uu____4585)  in
                   (FStar_Pervasives_Native.None, uu____4579)  in
                 [uu____4566]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4637,t1)::(pat2,uu____4640,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4736 =
            let uu____4737 =
              let uu____4744 = resugar_term' env e  in
              let uu____4745 = resugar_term' env t1  in
              let uu____4746 = resugar_term' env t2  in
              (uu____4744, uu____4745, uu____4746)  in
            FStar_Parser_AST.If uu____4737  in
          mk1 uu____4736
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4812 =
            match uu____4812 with
            | (pat,wopt,b) ->
                let uu____4854 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4854 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4906 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4906
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4910 =
            let uu____4911 =
              let uu____4926 = resugar_term' env e  in
              let uu____4927 = FStar_List.map resugar_branch branches  in
              (uu____4926, uu____4927)  in
            FStar_Parser_AST.Match uu____4911  in
          mk1 uu____4910
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4973) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5042 =
            let uu____5043 =
              let uu____5052 = resugar_term' env e  in
              (uu____5052, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5043  in
          mk1 uu____5042
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5081 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5081 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5135 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5135
                    in
                 let uu____5142 =
                   let uu____5147 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5147
                    in
                 match uu____5142 with
                 | (univs1,td) ->
                     let uu____5167 =
                       let uu____5174 =
                         let uu____5175 = FStar_Syntax_Subst.compress td  in
                         uu____5175.FStar_Syntax_Syntax.n  in
                       match uu____5174 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5184,(t1,uu____5186)::(d,uu____5188)::[])
                           -> (t1, d)
                       | uu____5245 -> failwith "wrong let binding format"
                        in
                     (match uu____5167 with
                      | (typ,def) ->
                          let uu____5276 =
                            let uu____5292 =
                              let uu____5293 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5293.FStar_Syntax_Syntax.n  in
                            match uu____5292 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5313) ->
                                let uu____5338 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5338 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5369 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5369
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5392 -> ([], def, false)  in
                          (match uu____5276 with
                           | (binders,term,is_pat_app) ->
                               let uu____5447 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5458 =
                                       let uu____5459 =
                                         let uu____5460 =
                                           let uu____5467 =
                                             bv_as_unique_ident bv  in
                                           (uu____5467,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5460
                                          in
                                       mk_pat uu____5459  in
                                     (uu____5458, term)
                                  in
                               (match uu____5447 with
                                | (pat,term1) ->
                                    let uu____5489 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5532  ->
                                                  match uu____5532 with
                                                  | (bv,q) ->
                                                      let uu____5547 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5547
                                                        (fun q1  ->
                                                           let uu____5559 =
                                                             let uu____5560 =
                                                               let uu____5567
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5567,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5560
                                                              in
                                                           mk_pat uu____5559)))
                                           in
                                        let uu____5570 =
                                          let uu____5575 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5575)
                                           in
                                        let uu____5578 =
                                          universe_to_string univs1  in
                                        (uu____5570, uu____5578)
                                      else
                                        (let uu____5587 =
                                           let uu____5592 =
                                             resugar_term' env term1  in
                                           (pat, uu____5592)  in
                                         let uu____5593 =
                                           universe_to_string univs1  in
                                         (uu____5587, uu____5593))
                                       in
                                    (attrs_opt, uu____5489))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5699 =
                   match uu____5699 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5759 =
                         let uu____5761 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5761  in
                       if uu____5759
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5842) ->
          let s =
            let uu____5861 =
              let uu____5863 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5863 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5861  in
          let uu____5868 = mk1 FStar_Parser_AST.Wild  in label s uu____5868
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5876 =
            let uu____5877 =
              let uu____5882 = resugar_term' env tm  in (uu____5882, qi1)  in
            FStar_Parser_AST.Quote uu____5877  in
          mk1 uu____5876
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___5_5894 =
            match uu___5_5894 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5902,(uu____5903,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____5964 =
                        let uu____5965 =
                          let uu____5974 = resugar_seq t11  in
                          (uu____5974, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____5965  in
                      mk1 uu____5964
                  | uu____5977 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____5978,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6042  ->
                         match uu____6042 with
                         | (x,uu____6050) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6055 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____6073,t1) ->
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
               let uu____6113 = FStar_Options.print_universes ()  in
               if uu____6113
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
               let uu____6177 = FStar_Options.print_universes ()  in
               if uu____6177
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
            let uu____6221 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6221, FStar_Parser_AST.Nothing)  in
          let uu____6222 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6222
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6245 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6245
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6330 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6330, (FStar_Pervasives_Native.snd post))  in
                    let uu____6341 =
                      let uu____6350 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6350 then [] else [pre]  in
                    let uu____6385 =
                      let uu____6394 =
                        let uu____6403 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6403 then [] else [pats]  in
                      FStar_List.append [post1] uu____6394  in
                    FStar_List.append uu____6341 uu____6385
                | uu____6462 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6496  ->
                   match uu____6496 with
                   | (e,uu____6508) ->
                       let uu____6513 = resugar_term' env e  in
                       (uu____6513, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___6_6538 =
              match uu___6_6538 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6571 = resugar_term' env e  in
                         (uu____6571, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6576 -> aux l tl1)
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
        let uu____6623 = b  in
        match uu____6623 with
        | (x,aq) ->
            let uu____6632 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6632
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6646 =
                       let uu____6647 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6647  in
                     FStar_Parser_AST.mk_binder uu____6646 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6648 ->
                     let uu____6649 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6649
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6654 =
                          let uu____6655 =
                            let uu____6660 = bv_as_unique_ident x  in
                            (uu____6660, e)  in
                          FStar_Parser_AST.Annotated uu____6655  in
                        FStar_Parser_AST.mk_binder uu____6654 r
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
              let uu____6680 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6680  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6684 =
                if used
                then
                  let uu____6686 =
                    let uu____6693 = bv_as_unique_ident v1  in
                    (uu____6693, aqual)  in
                  FStar_Parser_AST.PatVar uu____6686
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6684  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6700;
                  FStar_Syntax_Syntax.vars = uu____6701;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6711 = FStar_Options.print_bound_var_types ()  in
                if uu____6711
                then
                  let uu____6714 =
                    let uu____6715 =
                      let uu____6726 =
                        let uu____6733 = resugar_term' env typ  in
                        (uu____6733, FStar_Pervasives_Native.None)  in
                      (pat, uu____6726)  in
                    FStar_Parser_AST.PatAscribed uu____6715  in
                  mk1 uu____6714
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
          let uu____6754 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6754
            (fun aqual  ->
               let uu____6766 =
                 let uu____6771 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6782  -> FStar_Pervasives_Native.Some _6782)
                   uu____6771
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6766)

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
          (let uu____6844 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6844) &&
            (let uu____6847 =
               FStar_List.existsML
                 (fun uu____6860  ->
                    match uu____6860 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6882)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6887 -> false
                          | uu____6889 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6847)
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
            let uu____6957 = may_drop_implicits args  in
            if uu____6957 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6982  ->
                 match uu____6982 with
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
              ((let uu____7037 =
                  let uu____7039 =
                    let uu____7041 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7041  in
                  Prims.op_Negation uu____7039  in
                if uu____7037
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
              let uu____7085 = filter_pattern_imp args  in
              (match uu____7085 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7135 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7135 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7154 =
                       let uu____7160 =
                         let uu____7162 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7162
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7160)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7154);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7215  ->
                        match uu____7215 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7232 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7232)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7240;
                 FStar_Syntax_Syntax.fv_delta = uu____7241;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7270 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7270 FStar_List.rev  in
              let args1 =
                let uu____7286 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7306  ->
                          match uu____7306 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7286 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7384 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7384
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7407 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7407
                 in
              let args2 =
                let uu____7425 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7425 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7469 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7469 with
               | FStar_Pervasives_Native.Some (op,uu____7481) ->
                   let uu____7498 =
                     let uu____7499 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7499  in
                   mk1 uu____7498
               | FStar_Pervasives_Native.None  ->
                   let uu____7509 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7509 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7514 ->
              let uu____7515 =
                let uu____7516 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7516  in
              mk1 uu____7515
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
          let uu____7556 =
            let uu____7559 =
              let uu____7560 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7560  in
            FStar_Pervasives_Native.Some uu____7559  in
          FStar_Pervasives_Native.Some uu____7556

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
          let uu____7572 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7572

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___7_7580  ->
    match uu___7_7580 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7587 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7588 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7589 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7594 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7603 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7612 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___8_7618  ->
    match uu___8_7618 with
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
            (tylid,uvs,bs,t,uu____7661,datacons) ->
            let uu____7671 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7699,uu____7700,uu____7701,inductive_lid,uu____7703,uu____7704)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7711 -> failwith "unexpected"))
               in
            (match uu____7671 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7732 = FStar_Options.print_implicits ()  in
                   if uu____7732 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7749 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___9_7756  ->
                             match uu___9_7756 with
                             | FStar_Syntax_Syntax.RecordType uu____7758 ->
                                 true
                             | uu____7768 -> false))
                      in
                   if uu____7749
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7822,univs1,term,uu____7825,num,uu____7827)
                           ->
                           let uu____7834 =
                             let uu____7835 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7835.FStar_Syntax_Syntax.n  in
                           (match uu____7834 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7849)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7918  ->
                                          match uu____7918 with
                                          | (b,qual) ->
                                              let uu____7939 =
                                                bv_as_unique_ident b  in
                                              let uu____7940 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____7939, uu____7940,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____7951 -> failwith "unexpected")
                       | uu____7963 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____8094,num,uu____8096) ->
                            let c =
                              let uu____8117 =
                                let uu____8120 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8120  in
                              ((l.FStar_Ident.ident), uu____8117,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____8140 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8220 ->
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
        let uu____8246 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8246;
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
        let uu____8276 = ts  in
        match uu____8276 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8289 =
              let uu____8290 =
                let uu____8307 =
                  let uu____8316 =
                    let uu____8323 =
                      let uu____8324 =
                        let uu____8337 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8337)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8324  in
                    (uu____8323, FStar_Pervasives_Native.None)  in
                  [uu____8316]  in
                (false, false, uu____8307)  in
              FStar_Parser_AST.Tycon uu____8290  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8289
  
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
              let uu____8422 = resugar_tscheme'' env name ts  in [uu____8422]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8440 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8442 =
             let uu____8445 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8447 =
               let uu____8450 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8452 =
                 let uu____8455 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8457 =
                   let uu____8460 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8462 =
                     let uu____8465 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8467 =
                       let uu____8470 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8470 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8465 :: uu____8467  in
                   uu____8460 :: uu____8462  in
                 uu____8455 :: uu____8457  in
               uu____8450 :: uu____8452  in
             uu____8445 :: uu____8447  in
           uu____8440 :: uu____8442)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8500 =
        match uu____8500 with
        | (ts,uu____8507) -> resugar_tscheme'' env name ts  in
      let uu____8508 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8510 =
        let uu____8513 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8515 =
          let uu____8518 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8520 =
            let uu____8523 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8525 =
              let uu____8528 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8528]  in
            uu____8523 :: uu____8525  in
          uu____8518 :: uu____8520  in
        uu____8513 :: uu____8515  in
      uu____8508 :: uu____8510
  
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
            let uu____8589 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8589 with
            | (bs,action_defn) ->
                let uu____8596 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8596 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8606 = FStar_Options.print_implicits ()  in
                       if uu____8606
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8616 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8616 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8633 =
                           let uu____8644 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8644,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8633  in
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
          let uu____8728 =
            let uu____8733 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8733
             in
          match uu____8728 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8751 = FStar_Options.print_implicits ()  in
                if uu____8751 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8761 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8761 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8811) ->
          let uu____8820 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8843 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8861 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8869 -> false
                    | uu____8886 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8820 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8924 se1 =
                 match uu____8924 with
                 | (datacon_ses1,tycons) ->
                     let uu____8950 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8950 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8965 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8965 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____9000 =
                           let uu____9001 =
                             let uu____9002 =
                               let uu____9019 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____9019)  in
                             FStar_Parser_AST.Tycon uu____9002  in
                           decl'_to_decl se uu____9001  in
                         FStar_Pervasives_Native.Some uu____9000
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____9054,uu____9055,uu____9056,uu____9057,uu____9058)
                              ->
                              let uu____9065 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____9065
                          | uu____9068 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____9072 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9079) ->
          let uu____9084 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9092  ->
                    match uu___10_9092 with
                    | FStar_Syntax_Syntax.Projector (uu____9094,uu____9095)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9097 -> true
                    | uu____9099 -> false))
             in
          if uu____9084
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9134) ->
                 let uu____9163 =
                   let uu____9164 =
                     let uu____9165 =
                       let uu____9176 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9176)  in
                     FStar_Parser_AST.TopLevelLet uu____9165  in
                   decl'_to_decl se uu____9164  in
                 FStar_Pervasives_Native.Some uu____9163
             | uu____9213 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9218,fml) ->
          let uu____9220 =
            let uu____9221 =
              let uu____9222 =
                let uu____9227 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9227)  in
              FStar_Parser_AST.Assume uu____9222  in
            decl'_to_decl se uu____9221  in
          FStar_Pervasives_Native.Some uu____9220
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9229 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9229
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9238,t) ->
                let uu____9248 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9248
            | uu____9249 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9257,t) ->
                let uu____9267 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9267
            | uu____9268 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9292 -> failwith "Should not happen hopefully"  in
          let uu____9302 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9302
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9312 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9312 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9324 = FStar_Options.print_implicits ()  in
                 if uu____9324 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9340 =
                 let uu____9341 =
                   let uu____9342 =
                     let uu____9359 =
                       let uu____9368 =
                         let uu____9375 =
                           let uu____9376 =
                             let uu____9389 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9389)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9376  in
                         (uu____9375, FStar_Pervasives_Native.None)  in
                       [uu____9368]  in
                     (false, false, uu____9359)  in
                   FStar_Parser_AST.Tycon uu____9342  in
                 decl'_to_decl se uu____9341  in
               FStar_Pervasives_Native.Some uu____9340)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9421 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9421
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9425 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___11_9433  ->
                    match uu___11_9433 with
                    | FStar_Syntax_Syntax.Projector (uu____9435,uu____9436)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9438 -> true
                    | uu____9440 -> false))
             in
          if uu____9425
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9448 =
                 (let uu____9452 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9452) || (FStar_List.isEmpty uvs)
                  in
               if uu____9448
               then resugar_term' env t
               else
                 (let uu____9457 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9457 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9466 = resugar_term' env t1  in
                      label universes uu____9466)
                in
             let uu____9467 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9467)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9474 =
            let uu____9475 =
              let uu____9476 =
                let uu____9483 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9488 = resugar_term' env t  in
                (uu____9483, uu____9488)  in
              FStar_Parser_AST.Splice uu____9476  in
            decl'_to_decl se uu____9475  in
          FStar_Pervasives_Native.Some uu____9474
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9491 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9508 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9524 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9548 = noenv resugar_term'  in uu____9548 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9566 = noenv resugar_sigelt'  in uu____9566 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9584 = noenv resugar_comp'  in uu____9584 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9607 = noenv resugar_pat'  in uu____9607 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9641 = noenv resugar_binder'  in uu____9641 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9666 = noenv resugar_tscheme'  in uu____9666 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9694 = noenv resugar_eff_decl'  in uu____9694 r q ed
  