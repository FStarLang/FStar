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
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2657,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2658))::tl1 ->
                  drop_implicits tl1
              | uu____2677 -> args2  in
            let uu____2686 = drop_implicits args1  in
            match uu____2686 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2718::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2748 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2848  ->
                   match uu____2848 with
                   | (e2,qual) ->
                       let uu____2865 = resugar_term' env e2  in
                       let uu____2866 = resugar_imp env qual  in
                       (uu____2865, uu____2866)) args1
               in
            let uu____2867 = resugar_term' env e1  in
            match uu____2867 with
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
                     fun uu____2904  ->
                       match uu____2904 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2920 = FStar_Options.print_implicits ()  in
            if uu____2920 then args else filter_imp args  in
          let uu____2935 = resugar_term_as_op e  in
          (match uu____2935 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2948) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2973  ->
                        match uu____2973 with
                        | (x,uu____2985) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2994 =
                                   let uu____2995 =
                                     let uu____2996 =
                                       let uu____3003 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3003, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2996  in
                                   mk1 uu____2995  in
                                 FStar_Pervasives_Native.Some uu____2994))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3007) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____3033)::[] -> b
                 | uu____3050 -> failwith "wrong arguments to dtuple"  in
               let uu____3060 =
                 let uu____3061 = FStar_Syntax_Subst.compress body  in
                 uu____3061.FStar_Syntax_Syntax.n  in
               (match uu____3060 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3066) ->
                    let uu____3091 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3091 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3101 = FStar_Options.print_implicits ()
                              in
                           if uu____3101 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3118 =
                           let uu____3119 =
                             let uu____3130 =
                               FStar_List.map
                                 (fun _3141  -> FStar_Util.Inl _3141) xs3
                                in
                             (uu____3130, body3)  in
                           FStar_Parser_AST.Sum uu____3119  in
                         mk1 uu____3118)
                | uu____3148 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3171  ->
                              match uu____3171 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3189) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3198) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3207 = FStar_List.hd args1  in
               (match uu____3207 with
                | (t1,uu____3221) ->
                    let uu____3226 =
                      let uu____3227 = FStar_Syntax_Subst.compress t1  in
                      uu____3227.FStar_Syntax_Syntax.n  in
                    (match uu____3226 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3234 =
                           let uu____3235 =
                             let uu____3240 = resugar_term' env t1  in
                             (uu____3240, f)  in
                           FStar_Parser_AST.Project uu____3235  in
                         mk1 uu____3234
                     | uu____3241 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3242) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___424_3269  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3279 =
                           match new_args with
                           | (a1,uu____3289)::(a2,uu____3291)::[] -> (a1, a2)
                           | uu____3318 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3279 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3340 =
                                  let uu____3341 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3341.FStar_Syntax_Syntax.n  in
                                match uu____3340 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3346) ->
                                    let uu____3371 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3371 with | (x1,e2) -> e2)
                                | uu____3378 ->
                                    let uu____3379 =
                                      let uu____3381 =
                                        let uu____3383 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3383
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3381
                                       in
                                    failwith uu____3379
                                 in
                              let body1 =
                                let uu____3386 = decomp body  in
                                resugar_term' env uu____3386  in
                              let handler1 =
                                let uu____3388 = decomp handler  in
                                resugar_term' env uu____3388  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3396,uu____3397,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3429,uu____3430,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3467 =
                                      let uu____3468 =
                                        let uu____3477 = resugar_body t11  in
                                        (uu____3477, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3468
                                       in
                                    mk1 uu____3467
                                | uu____3480 ->
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
                                | uu____3538 -> []  in
                              let branches = resugar_branches handler1  in
                              mk1 (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3571 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3572) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3581) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3602) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,(uu____3667,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,(uu____3699,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3730 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3743 =
                   let uu____3744 = FStar_Syntax_Subst.compress body  in
                   uu____3744.FStar_Syntax_Syntax.n  in
                 match uu____3743 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3749) ->
                     let uu____3774 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3774 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3784 = FStar_Options.print_implicits ()
                               in
                            if uu____3784 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3800 =
                            let uu____3809 =
                              let uu____3810 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3810.FStar_Syntax_Syntax.n  in
                            match uu____3809 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3828 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3845,pats) ->
                                      let uu____3879 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3923  ->
                                                     match uu____3923 with
                                                     | (e2,uu____3931) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3879, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3947 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3947)
                                  | uu____3956 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3828 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3988 ->
                                let uu____3989 = resugar_term' env body2  in
                                ([], uu____3989)
                             in
                          (match uu____3800 with
                           | (pats,body3) ->
                               let uu____4006 = uncurry xs3 pats body3  in
                               (match uu____4006 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      let uu____4044 =
                                        let uu____4045 =
                                          let uu____4064 =
                                            let uu____4075 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs5 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4075, pats1)  in
                                          (xs5, uu____4064, body4)  in
                                        FStar_Parser_AST.QForall uu____4045
                                         in
                                      mk1 uu____4044
                                    else
                                      (let uu____4098 =
                                         let uu____4099 =
                                           let uu____4118 =
                                             let uu____4129 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs5
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4129, pats1)  in
                                           (xs5, uu____4118, body4)  in
                                         FStar_Parser_AST.QExists uu____4099
                                          in
                                       mk1 uu____4098))))
                 | uu____4150 ->
                     if op = "forall"
                     then
                       let uu____4154 =
                         let uu____4155 =
                           let uu____4174 = resugar_term' env body  in
                           ([], ([], []), uu____4174)  in
                         FStar_Parser_AST.QForall uu____4155  in
                       mk1 uu____4154
                     else
                       (let uu____4197 =
                          let uu____4198 =
                            let uu____4217 = resugar_term' env body  in
                            ([], ([], []), uu____4217)  in
                          FStar_Parser_AST.QExists uu____4198  in
                        mk1 uu____4197)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4256)::[] -> resugar b
                  | uu____4273 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4285) ->
               let uu____4293 = FStar_List.hd args1  in
               (match uu____4293 with
                | (e1,uu____4307) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4379  ->
                         match uu____4379 with
                         | (e1,qual) ->
                             let uu____4396 = resugar_term' env e1  in
                             let uu____4397 = resugar_imp env qual  in
                             (uu____4396, uu____4397)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4413 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4413 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4461 =
                               let uu____4462 =
                                 let uu____4469 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4469)  in
                               FStar_Parser_AST.Op uu____4462  in
                             mk1 uu____4461  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4487  ->
                                  match uu____4487 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4506 =
                      let uu____4507 =
                        let uu____4514 =
                          let uu____4517 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4517
                           in
                        (op1, uu____4514)  in
                      FStar_Parser_AST.Op uu____4507  in
                    mk1 uu____4506
                | uu____4530 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4599 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4599 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4645 =
                   let uu____4658 =
                     let uu____4663 = resugar_pat' env pat1 branch_bv  in
                     let uu____4664 = resugar_term' env e  in
                     (uu____4663, uu____4664)  in
                   (FStar_Pervasives_Native.None, uu____4658)  in
                 [uu____4645]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4716,t1)::(pat2,uu____4719,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4815 =
            let uu____4816 =
              let uu____4823 = resugar_term' env e  in
              let uu____4824 = resugar_term' env t1  in
              let uu____4825 = resugar_term' env t2  in
              (uu____4823, uu____4824, uu____4825)  in
            FStar_Parser_AST.If uu____4816  in
          mk1 uu____4815
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4891 =
            match uu____4891 with
            | (pat,wopt,b) ->
                let uu____4933 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4933 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4985 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4985
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4989 =
            let uu____4990 =
              let uu____5005 = resugar_term' env e  in
              let uu____5006 = FStar_List.map resugar_branch branches  in
              (uu____5005, uu____5006)  in
            FStar_Parser_AST.Match uu____4990  in
          mk1 uu____4989
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5052) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5121 =
            let uu____5122 =
              let uu____5131 = resugar_term' env e  in
              (uu____5131, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5122  in
          mk1 uu____5121
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5160 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5160 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5214 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5214
                    in
                 let uu____5221 =
                   let uu____5226 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5226
                    in
                 match uu____5221 with
                 | (univs1,td) ->
                     let uu____5246 =
                       let uu____5253 =
                         let uu____5254 = FStar_Syntax_Subst.compress td  in
                         uu____5254.FStar_Syntax_Syntax.n  in
                       match uu____5253 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5263,(t1,uu____5265)::(d,uu____5267)::[])
                           -> (t1, d)
                       | uu____5324 -> failwith "wrong let binding format"
                        in
                     (match uu____5246 with
                      | (typ,def) ->
                          let uu____5355 =
                            let uu____5371 =
                              let uu____5372 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5372.FStar_Syntax_Syntax.n  in
                            match uu____5371 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5392) ->
                                let uu____5417 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5417 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5448 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5448
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5471 -> ([], def, false)  in
                          (match uu____5355 with
                           | (binders,term,is_pat_app) ->
                               let uu____5526 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5537 =
                                       let uu____5538 =
                                         let uu____5539 =
                                           let uu____5546 =
                                             bv_as_unique_ident bv  in
                                           (uu____5546,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5539
                                          in
                                       mk_pat uu____5538  in
                                     (uu____5537, term)
                                  in
                               (match uu____5526 with
                                | (pat,term1) ->
                                    let uu____5568 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5611  ->
                                                  match uu____5611 with
                                                  | (bv,q) ->
                                                      let uu____5626 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5626
                                                        (fun q1  ->
                                                           let uu____5638 =
                                                             let uu____5639 =
                                                               let uu____5646
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5646,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5639
                                                              in
                                                           mk_pat uu____5638)))
                                           in
                                        let uu____5649 =
                                          let uu____5654 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5654)
                                           in
                                        let uu____5657 =
                                          universe_to_string univs1  in
                                        (uu____5649, uu____5657)
                                      else
                                        (let uu____5666 =
                                           let uu____5671 =
                                             resugar_term' env term1  in
                                           (pat, uu____5671)  in
                                         let uu____5672 =
                                           universe_to_string univs1  in
                                         (uu____5666, uu____5672))
                                       in
                                    (attrs_opt, uu____5568))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5778 =
                   match uu____5778 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5838 =
                         let uu____5840 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5840  in
                       if uu____5838
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5921) ->
          let s =
            let uu____5940 =
              let uu____5942 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5942 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5940  in
          let uu____5947 = mk1 FStar_Parser_AST.Wild  in label s uu____5947
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5955 =
            let uu____5956 =
              let uu____5961 = resugar_term' env tm  in (uu____5961, qi1)  in
            FStar_Parser_AST.Quote uu____5956  in
          mk1 uu____5955
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_5973 =
            match uu___4_5973 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5981,(uu____5982,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6043 =
                        let uu____6044 =
                          let uu____6053 = resugar_seq t11  in
                          (uu____6053, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6044  in
                      mk1 uu____6043
                  | uu____6056 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6057,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6121  ->
                         match uu____6121 with
                         | (x,uu____6129) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6134 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____6152,t1) ->
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
               let uu____6192 = FStar_Options.print_universes ()  in
               if uu____6192
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
               let uu____6256 = FStar_Options.print_universes ()  in
               if uu____6256
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
            let uu____6300 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6300, FStar_Parser_AST.Nothing)  in
          let uu____6301 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6301
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6324 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6324
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6409 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6409, (FStar_Pervasives_Native.snd post))  in
                    let uu____6420 =
                      let uu____6429 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6429 then [] else [pre]  in
                    let uu____6464 =
                      let uu____6473 =
                        let uu____6482 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6482 then [] else [pats]  in
                      FStar_List.append [post1] uu____6473  in
                    FStar_List.append uu____6420 uu____6464
                | uu____6541 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6575  ->
                   match uu____6575 with
                   | (e,uu____6587) ->
                       let uu____6592 = resugar_term' env e  in
                       (uu____6592, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6617 =
              match uu___5_6617 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6650 = resugar_term' env e  in
                         (uu____6650, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6655 -> aux l tl1)
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
        let uu____6702 = b  in
        match uu____6702 with
        | (x,aq) ->
            let uu____6711 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6711
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6725 =
                       let uu____6726 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6726  in
                     FStar_Parser_AST.mk_binder uu____6725 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6727 ->
                     let uu____6728 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6728
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6733 =
                          let uu____6734 =
                            let uu____6739 = bv_as_unique_ident x  in
                            (uu____6739, e)  in
                          FStar_Parser_AST.Annotated uu____6734  in
                        FStar_Parser_AST.mk_binder uu____6733 r
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
              let uu____6759 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6759  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6763 =
                if used
                then
                  let uu____6765 =
                    let uu____6772 = bv_as_unique_ident v1  in
                    (uu____6772, aqual)  in
                  FStar_Parser_AST.PatVar uu____6765
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6763  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6779;
                  FStar_Syntax_Syntax.vars = uu____6780;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6790 = FStar_Options.print_bound_var_types ()  in
                if uu____6790
                then
                  let uu____6793 =
                    let uu____6794 =
                      let uu____6805 =
                        let uu____6812 = resugar_term' env typ  in
                        (uu____6812, FStar_Pervasives_Native.None)  in
                      (pat, uu____6805)  in
                    FStar_Parser_AST.PatAscribed uu____6794  in
                  mk1 uu____6793
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
          let uu____6833 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6833
            (fun aqual  ->
               let uu____6845 =
                 let uu____6850 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6861  -> FStar_Pervasives_Native.Some _6861)
                   uu____6850
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6845)

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
          (let uu____6923 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6923) &&
            (let uu____6926 =
               FStar_List.existsML
                 (fun uu____6939  ->
                    match uu____6939 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6961)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6966 -> false
                          | uu____6968 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6926)
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
            let uu____7036 = may_drop_implicits args  in
            if uu____7036 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7061  ->
                 match uu____7061 with
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
              ((let uu____7116 =
                  let uu____7118 =
                    let uu____7120 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7120  in
                  Prims.op_Negation uu____7118  in
                if uu____7116
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
              let uu____7164 = filter_pattern_imp args  in
              (match uu____7164 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7214 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7214 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7233 =
                       let uu____7239 =
                         let uu____7241 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7241
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7239)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7233);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7294  ->
                        match uu____7294 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7311 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7311)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7319;
                 FStar_Syntax_Syntax.fv_delta = uu____7320;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7349 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7349 FStar_List.rev  in
              let args1 =
                let uu____7365 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7385  ->
                          match uu____7385 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7365 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7463 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7463
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7486 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7486
                 in
              let args2 =
                let uu____7504 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7504 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7548 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7548 with
               | FStar_Pervasives_Native.Some (op,uu____7560) ->
                   let uu____7577 =
                     let uu____7578 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7578  in
                   mk1 uu____7577
               | FStar_Pervasives_Native.None  ->
                   let uu____7588 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7588 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7593 ->
              let uu____7594 =
                let uu____7595 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7595  in
              mk1 uu____7594
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
          let uu____7635 =
            let uu____7638 =
              let uu____7639 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7639  in
            FStar_Pervasives_Native.Some uu____7638  in
          FStar_Pervasives_Native.Some uu____7635

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
          let uu____7651 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7651

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7659  ->
    match uu___6_7659 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7666 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7667 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7668 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7673 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7682 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7691 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7697  ->
    match uu___7_7697 with
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
            (tylid,uvs,bs,t,uu____7740,datacons) ->
            let uu____7750 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7778,uu____7779,uu____7780,inductive_lid,uu____7782,uu____7783)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7790 -> failwith "unexpected"))
               in
            (match uu____7750 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7811 = FStar_Options.print_implicits ()  in
                   if uu____7811 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7828 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7835  ->
                             match uu___8_7835 with
                             | FStar_Syntax_Syntax.RecordType uu____7837 ->
                                 true
                             | uu____7847 -> false))
                      in
                   if uu____7828
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7901,univs1,term,uu____7904,num,uu____7906)
                           ->
                           let uu____7913 =
                             let uu____7914 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7914.FStar_Syntax_Syntax.n  in
                           (match uu____7913 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7928)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7997  ->
                                          match uu____7997 with
                                          | (b,qual) ->
                                              let uu____8018 =
                                                bv_as_unique_ident b  in
                                              let uu____8019 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8018, uu____8019,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8030 -> failwith "unexpected")
                       | uu____8042 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____8173,num,uu____8175) ->
                            let c =
                              let uu____8196 =
                                let uu____8199 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8199  in
                              ((l.FStar_Ident.ident), uu____8196,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____8219 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8299 ->
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
        let uu____8325 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8325;
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
        let uu____8355 = ts  in
        match uu____8355 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8368 =
              let uu____8369 =
                let uu____8386 =
                  let uu____8395 =
                    let uu____8402 =
                      let uu____8403 =
                        let uu____8416 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8416)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8403  in
                    (uu____8402, FStar_Pervasives_Native.None)  in
                  [uu____8395]  in
                (false, false, uu____8386)  in
              FStar_Parser_AST.Tycon uu____8369  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8368
  
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
              let uu____8501 = resugar_tscheme'' env name ts  in [uu____8501]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8519 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8521 =
             let uu____8524 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8526 =
               let uu____8529 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8531 =
                 let uu____8534 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8536 =
                   let uu____8539 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8541 =
                     let uu____8544 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8546 =
                       let uu____8549 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8549 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8544 :: uu____8546  in
                   uu____8539 :: uu____8541  in
                 uu____8534 :: uu____8536  in
               uu____8529 :: uu____8531  in
             uu____8524 :: uu____8526  in
           uu____8519 :: uu____8521)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8579 =
        match uu____8579 with
        | (ts,uu____8586) -> resugar_tscheme'' env name ts  in
      let uu____8587 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8589 =
        let uu____8592 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8594 =
          let uu____8597 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8599 =
            let uu____8602 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8604 =
              let uu____8607 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8607]  in
            uu____8602 :: uu____8604  in
          uu____8597 :: uu____8599  in
        uu____8592 :: uu____8594  in
      uu____8587 :: uu____8589
  
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
            let uu____8668 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8668 with
            | (bs,action_defn) ->
                let uu____8675 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8675 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8685 = FStar_Options.print_implicits ()  in
                       if uu____8685
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8695 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8695 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8712 =
                           let uu____8723 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8723,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8712  in
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
          let uu____8807 =
            let uu____8812 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8812
             in
          match uu____8807 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8830 = FStar_Options.print_implicits ()  in
                if uu____8830 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8840 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8840 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8890) ->
          let uu____8899 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8922 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8940 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8948 -> false
                    | uu____8965 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8899 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____9003 se1 =
                 match uu____9003 with
                 | (datacon_ses1,tycons) ->
                     let uu____9029 = resugar_typ env datacon_ses1 se1  in
                     (match uu____9029 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____9044 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____9044 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____9079 =
                           let uu____9080 =
                             let uu____9081 =
                               let uu____9098 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____9098)  in
                             FStar_Parser_AST.Tycon uu____9081  in
                           decl'_to_decl se uu____9080  in
                         FStar_Pervasives_Native.Some uu____9079
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____9133,uu____9134,uu____9135,uu____9136,uu____9137)
                              ->
                              let uu____9144 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____9144
                          | uu____9147 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____9151 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9158) ->
          let uu____9163 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_9171  ->
                    match uu___9_9171 with
                    | FStar_Syntax_Syntax.Projector (uu____9173,uu____9174)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9176 -> true
                    | uu____9178 -> false))
             in
          if uu____9163
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9213) ->
                 let uu____9242 =
                   let uu____9243 =
                     let uu____9244 =
                       let uu____9255 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9255)  in
                     FStar_Parser_AST.TopLevelLet uu____9244  in
                   decl'_to_decl se uu____9243  in
                 FStar_Pervasives_Native.Some uu____9242
             | uu____9292 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9297,fml) ->
          let uu____9299 =
            let uu____9300 =
              let uu____9301 =
                let uu____9306 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9306)  in
              FStar_Parser_AST.Assume uu____9301  in
            decl'_to_decl se uu____9300  in
          FStar_Pervasives_Native.Some uu____9299
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9308 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9308
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9317,t) ->
                let uu____9327 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9327
            | uu____9328 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9336,t) ->
                let uu____9346 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9346
            | uu____9347 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9371 -> failwith "Should not happen hopefully"  in
          let uu____9381 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9381
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9391 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9391 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9403 = FStar_Options.print_implicits ()  in
                 if uu____9403 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9419 =
                 let uu____9420 =
                   let uu____9421 =
                     let uu____9438 =
                       let uu____9447 =
                         let uu____9454 =
                           let uu____9455 =
                             let uu____9468 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9468)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9455  in
                         (uu____9454, FStar_Pervasives_Native.None)  in
                       [uu____9447]  in
                     (false, false, uu____9438)  in
                   FStar_Parser_AST.Tycon uu____9421  in
                 decl'_to_decl se uu____9420  in
               FStar_Pervasives_Native.Some uu____9419)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9500 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9500
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9504 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9512  ->
                    match uu___10_9512 with
                    | FStar_Syntax_Syntax.Projector (uu____9514,uu____9515)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9517 -> true
                    | uu____9519 -> false))
             in
          if uu____9504
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9527 =
                 (let uu____9531 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9531) || (FStar_List.isEmpty uvs)
                  in
               if uu____9527
               then resugar_term' env t
               else
                 (let uu____9536 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9536 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9545 = resugar_term' env t1  in
                      label universes uu____9545)
                in
             let uu____9546 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9546)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9553 =
            let uu____9554 =
              let uu____9555 =
                let uu____9562 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9567 = resugar_term' env t  in
                (uu____9562, uu____9567)  in
              FStar_Parser_AST.Splice uu____9555  in
            decl'_to_decl se uu____9554  in
          FStar_Pervasives_Native.Some uu____9553
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9570 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9587 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9603 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9627 = noenv resugar_term'  in uu____9627 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9645 = noenv resugar_sigelt'  in uu____9645 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9663 = noenv resugar_comp'  in uu____9663 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9686 = noenv resugar_pat'  in uu____9686 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9720 = noenv resugar_binder'  in uu____9720 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9745 = noenv resugar_tscheme'  in uu____9745 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9773 = noenv resugar_eff_decl'  in uu____9773 r q ed
  