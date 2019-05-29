open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
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
          universe_to_int (n1 + (Prims.parse_int "1")) u1
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
          let uu____343 = universe_to_int (Prims.parse_int "0") u  in
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
               let op =
                 let uu____1019 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____1073) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____1019
                  in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
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
      let uu____1400 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1400 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1470 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
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
                (let uu____1572 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1572
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1608 =
      let uu____1609 = FStar_Syntax_Subst.compress t  in
      uu____1609.FStar_Syntax_Syntax.n  in
    match uu____1608 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let uu____1630 = string_to_op s  in
        (match uu____1630 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1670 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1687 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1704 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1715 -> true
    | uu____1717 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1738 ->
        let uu____1740 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1740
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1754 = may_shorten lid  in
      if uu____1754 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1899 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1899  in
      let uu____1902 =
        let uu____1903 = FStar_Syntax_Subst.compress t  in
        uu____1903.FStar_Syntax_Syntax.n  in
      match uu____1902 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1906 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1931 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1931
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1934 =
              let uu____1937 = bv_as_unique_ident x  in [uu____1937]  in
            FStar_Ident.lid_of_ids uu____1934  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1940 =
              let uu____1943 = bv_as_unique_ident x  in [uu____1943]  in
            FStar_Ident.lid_of_ids uu____1940  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length1 = (Prims.parse_int "0")
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____1962 =
              let uu____1963 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1963  in
            mk1 uu____1962
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
               | uu____1987 -> failwith "wrong projector format")
            else
              (let uu____1994 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1998 =
                      let uu____2000 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____2000  in
                    let uu____2003 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1998 <> uu____2003)
                  in
               if uu____1994
               then
                 let uu____2008 =
                   let uu____2009 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____2009  in
                 mk1 uu____2008
               else
                 (let uu____2012 =
                    let uu____2013 =
                      let uu____2024 = maybe_shorten_fv env fv  in
                      (uu____2024, [])  in
                    FStar_Parser_AST.Construct uu____2013  in
                  mk1 uu____2012))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2042 = FStar_Options.print_universes ()  in
          if uu____2042
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
                   let uu____2073 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2073  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2096 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2104 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2104
          then
            let uu____2107 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2107
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2112 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2133 -> ("Type", true)  in
          (match uu____2112 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2145 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2145  in
               let uu____2146 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2146
               then
                 let uu____2149 =
                   let uu____2150 =
                     let uu____2157 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2157, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2150  in
                 mk1 uu____2149
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2162) ->
          let uu____2187 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2187 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2203 = FStar_Options.print_implicits ()  in
                 if uu____2203 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2241  ->
                         match uu____2241 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2281 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2281 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2291 = FStar_Options.print_implicits ()  in
                 if uu____2291 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2302 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2302 FStar_List.rev  in
               let rec aux body3 uu___2_2327 =
                 match uu___2_2327 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2343 =
            let uu____2348 =
              let uu____2349 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2349]  in
            FStar_Syntax_Subst.open_term uu____2348 phi  in
          (match uu____2343 with
           | (x1,phi1) ->
               let b =
                 let uu____2371 =
                   let uu____2374 = FStar_List.hd x1  in
                   resugar_binder' env uu____2374 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2371  in
               let uu____2381 =
                 let uu____2382 =
                   let uu____2387 = resugar_term' env phi1  in
                   (b, uu____2387)  in
                 FStar_Parser_AST.Refine uu____2382  in
               mk1 uu____2381)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2389;
             FStar_Syntax_Syntax.vars = uu____2390;_},(e,uu____2392)::[])
          when
          (let uu____2433 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2433) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2482 =
            match uu___3_2482 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2552 -> failwith "last of an empty list"  in
          let rec last_two uu___4_2591 =
            match uu___4_2591 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____2623::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2701::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2772  ->
                   match uu____2772 with
                   | (e2,qual) ->
                       let uu____2789 = resugar_term' env e2  in
                       let uu____2790 = resugar_imp env qual  in
                       (uu____2789, uu____2790)) args1
               in
            let uu____2791 = resugar_term' env e1  in
            match uu____2791 with
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
                     fun uu____2828  ->
                       match uu____2828 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2844 = FStar_Options.print_implicits ()  in
            if uu____2844 then args else filter_imp args  in
          let uu____2859 = resugar_term_as_op e  in
          (match uu____2859 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2872) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2897  ->
                        match uu____2897 with
                        | (x,uu____2909) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2918 =
                                   let uu____2919 =
                                     let uu____2920 =
                                       let uu____2927 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2927, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2920  in
                                   mk1 uu____2919  in
                                 FStar_Pervasives_Native.Some uu____2918))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2931) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2957)::[] -> b
                 | uu____2974 -> failwith "wrong arguments to dtuple"  in
               let uu____2984 =
                 let uu____2985 = FStar_Syntax_Subst.compress body  in
                 uu____2985.FStar_Syntax_Syntax.n  in
               (match uu____2984 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2990) ->
                    let uu____3015 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3015 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3025 = FStar_Options.print_implicits ()
                              in
                           if uu____3025 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3042 =
                           let uu____3043 =
                             let uu____3054 =
                               FStar_List.map
                                 (fun _3065  -> FStar_Util.Inl _3065) xs3
                                in
                             (uu____3054, body3)  in
                           FStar_Parser_AST.Sum uu____3043  in
                         mk1 uu____3042)
                | uu____3072 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3095  ->
                              match uu____3095 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3113) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3122) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3131 = FStar_List.hd args1  in
               (match uu____3131 with
                | (t1,uu____3145) ->
                    let uu____3150 =
                      let uu____3151 = FStar_Syntax_Subst.compress t1  in
                      uu____3151.FStar_Syntax_Syntax.n  in
                    (match uu____3150 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3158 =
                           let uu____3159 =
                             let uu____3164 = resugar_term' env t1  in
                             (uu____3164, f)  in
                           FStar_Parser_AST.Project uu____3159  in
                         mk1 uu____3158
                     | uu____3165 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3166) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____3190 =
                 match new_args with
                 | (a1,uu____3200)::(a2,uu____3202)::[] -> (a1, a2)
                 | uu____3229 -> failwith "wrong arguments to try_with"  in
               (match uu____3190 with
                | (body,handler) ->
                    let decomp term =
                      let uu____3251 =
                        let uu____3252 = FStar_Syntax_Subst.compress term  in
                        uu____3252.FStar_Syntax_Syntax.n  in
                      match uu____3251 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____3257) ->
                          let uu____3282 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____3282 with | (x1,e2) -> e2)
                      | uu____3289 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____3292 = decomp body  in
                      resugar_term' env uu____3292  in
                    let handler1 =
                      let uu____3294 = decomp handler  in
                      resugar_term' env uu____3294  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____3302,uu____3303,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____3335,uu____3336,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____3373 =
                            let uu____3374 =
                              let uu____3383 = resugar_body t11  in
                              (uu____3383, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____3374  in
                          mk1 uu____3373
                      | uu____3386 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____3444 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____3474) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3483) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3504) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 np =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists
                     (x,uu____3582,(uu____3583,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body np
                 | FStar_Parser_AST.QForall
                     (x,uu____3617,(uu____3618,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body np
                 | uu____3651 -> (xs, pat, t1, np)  in
               let resugar body =
                 let uu____3665 =
                   let uu____3666 = FStar_Syntax_Subst.compress body  in
                   uu____3666.FStar_Syntax_Syntax.n  in
                 match uu____3665 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3671) ->
                     let uu____3696 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3696 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3706 = FStar_Options.print_implicits ()
                               in
                            if uu____3706 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3722 =
                            let uu____3734 =
                              let uu____3735 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3735.FStar_Syntax_Syntax.n  in
                            match uu____3734 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3756 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3779,pats,np) ->
                                      let uu____3816 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3860  ->
                                                     match uu____3860 with
                                                     | (e2,uu____3868) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3816, body3, np)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3885 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3885, false)
                                  | uu____3896 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3756 with
                                 | (pats,body4,np) -> (pats, body4, np))
                            | uu____3938 ->
                                let uu____3939 = resugar_term' env body2  in
                                ([], uu____3939, false)
                             in
                          (match uu____3722 with
                           | (pats,body3,np) ->
                               let uu____3961 = uncurry xs3 pats body3 np  in
                               (match uu____3961 with
                                | (xs4,pats1,body4,np1) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      let uu____4005 =
                                        let uu____4006 =
                                          let uu____4028 =
                                            let uu____4039 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs5 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4039, pats1)  in
                                          (xs5, np1, uu____4028, body4)  in
                                        FStar_Parser_AST.QForall uu____4006
                                         in
                                      mk1 uu____4005
                                    else
                                      (let uu____4063 =
                                         let uu____4064 =
                                           let uu____4086 =
                                             let uu____4097 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs5
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4097, pats1)  in
                                           (xs5, np1, uu____4086, body4)  in
                                         FStar_Parser_AST.QExists uu____4064
                                          in
                                       mk1 uu____4063))))
                 | uu____4119 ->
                     if op = "forall"
                     then
                       let uu____4123 =
                         let uu____4124 =
                           let uu____4146 = resugar_term' env body  in
                           ([], false, ([], []), uu____4146)  in
                         FStar_Parser_AST.QForall uu____4124  in
                       mk1 uu____4123
                     else
                       (let uu____4171 =
                          let uu____4172 =
                            let uu____4194 = resugar_term' env body  in
                            ([], false, ([], []), uu____4194)  in
                          FStar_Parser_AST.QExists uu____4172  in
                        mk1 uu____4171)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4235)::[] -> resugar b
                  | uu____4252 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4264) ->
               let uu____4272 = FStar_List.hd args1  in
               (match uu____4272 with
                | (e1,uu____4286) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4358  ->
                         match uu____4358 with
                         | (e1,qual) ->
                             let uu____4375 = resugar_term' env e1  in
                             let uu____4376 = resugar_imp env qual  in
                             (uu____4375, uu____4376)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4392 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4392 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4440 =
                               let uu____4441 =
                                 let uu____4448 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4448)  in
                               FStar_Parser_AST.Op uu____4441  in
                             mk1 uu____4440  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4466  ->
                                  match uu____4466 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4485 =
                      let uu____4486 =
                        let uu____4493 =
                          let uu____4496 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4496
                           in
                        (op1, uu____4493)  in
                      FStar_Parser_AST.Op uu____4486  in
                    mk1 uu____4485
                | uu____4509 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4578 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4578 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4624 =
                   let uu____4637 =
                     let uu____4642 = resugar_pat' env pat1 branch_bv  in
                     let uu____4643 = resugar_term' env e  in
                     (uu____4642, uu____4643)  in
                   (FStar_Pervasives_Native.None, uu____4637)  in
                 [uu____4624]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4695,t1)::(pat2,uu____4698,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4794 =
            let uu____4795 =
              let uu____4802 = resugar_term' env e  in
              let uu____4803 = resugar_term' env t1  in
              let uu____4804 = resugar_term' env t2  in
              (uu____4802, uu____4803, uu____4804)  in
            FStar_Parser_AST.If uu____4795  in
          mk1 uu____4794
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4870 =
            match uu____4870 with
            | (pat,wopt,b) ->
                let uu____4912 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4912 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4964 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4964
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4968 =
            let uu____4969 =
              let uu____4984 = resugar_term' env e  in
              let uu____4985 = FStar_List.map resugar_branch branches  in
              (uu____4984, uu____4985)  in
            FStar_Parser_AST.Match uu____4969  in
          mk1 uu____4968
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5031) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5100 =
            let uu____5101 =
              let uu____5110 = resugar_term' env e  in
              (uu____5110, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5101  in
          mk1 uu____5100
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5139 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5139 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5193 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5193
                    in
                 let uu____5200 =
                   let uu____5205 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5205
                    in
                 match uu____5200 with
                 | (univs1,td) ->
                     let uu____5225 =
                       let uu____5232 =
                         let uu____5233 = FStar_Syntax_Subst.compress td  in
                         uu____5233.FStar_Syntax_Syntax.n  in
                       match uu____5232 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5242,(t1,uu____5244)::(d,uu____5246)::[])
                           -> (t1, d)
                       | uu____5303 -> failwith "wrong let binding format"
                        in
                     (match uu____5225 with
                      | (typ,def) ->
                          let uu____5334 =
                            let uu____5350 =
                              let uu____5351 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5351.FStar_Syntax_Syntax.n  in
                            match uu____5350 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5371) ->
                                let uu____5396 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5396 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5427 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5427
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5450 -> ([], def, false)  in
                          (match uu____5334 with
                           | (binders,term,is_pat_app) ->
                               let uu____5505 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5516 =
                                       let uu____5517 =
                                         let uu____5518 =
                                           let uu____5525 =
                                             bv_as_unique_ident bv  in
                                           (uu____5525,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5518
                                          in
                                       mk_pat uu____5517  in
                                     (uu____5516, term)
                                  in
                               (match uu____5505 with
                                | (pat,term1) ->
                                    let uu____5547 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5590  ->
                                                  match uu____5590 with
                                                  | (bv,q) ->
                                                      let uu____5605 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5605
                                                        (fun q1  ->
                                                           let uu____5617 =
                                                             let uu____5618 =
                                                               let uu____5625
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5625,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5618
                                                              in
                                                           mk_pat uu____5617)))
                                           in
                                        let uu____5628 =
                                          let uu____5633 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5633)
                                           in
                                        let uu____5636 =
                                          universe_to_string univs1  in
                                        (uu____5628, uu____5636)
                                      else
                                        (let uu____5645 =
                                           let uu____5650 =
                                             resugar_term' env term1  in
                                           (pat, uu____5650)  in
                                         let uu____5651 =
                                           universe_to_string univs1  in
                                         (uu____5645, uu____5651))
                                       in
                                    (attrs_opt, uu____5547))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5757 =
                   match uu____5757 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5817 =
                         let uu____5819 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5819  in
                       if uu____5817
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5900) ->
          let s =
            let uu____5919 =
              let uu____5921 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5921 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5919  in
          let uu____5926 = mk1 FStar_Parser_AST.Wild  in label s uu____5926
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5934 =
            let uu____5935 =
              let uu____5940 = resugar_term' env tm  in (uu____5940, qi1)  in
            FStar_Parser_AST.Quote uu____5935  in
          mk1 uu____5934
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___5_5952 =
            match uu___5_5952 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5960,(uu____5961,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6022 =
                        let uu____6023 =
                          let uu____6032 = resugar_seq t11  in
                          (uu____6032, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6023  in
                      mk1 uu____6022
                  | uu____6035 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6036,pats,uu____6038) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6103  ->
                         match uu____6103 with
                         | (x,uu____6111) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6116 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____6134,t1) ->
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
               let uu____6174 = FStar_Options.print_universes ()  in
               if uu____6174
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
               let uu____6238 = FStar_Options.print_universes ()  in
               if uu____6238
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
            let uu____6282 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6282, FStar_Parser_AST.Nothing)  in
          let uu____6283 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6283
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6306 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6306
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6391 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6391, (FStar_Pervasives_Native.snd post))  in
                    let uu____6402 =
                      let uu____6411 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6411 then [] else [pre]  in
                    let uu____6446 =
                      let uu____6455 =
                        let uu____6464 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6464 then [] else [pats]  in
                      FStar_List.append [post1] uu____6455  in
                    FStar_List.append uu____6402 uu____6446
                | uu____6523 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6557  ->
                   match uu____6557 with
                   | (e,uu____6569) ->
                       let uu____6574 = resugar_term' env e  in
                       (uu____6574, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___6_6599 =
              match uu___6_6599 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6632 = resugar_term' env e  in
                         (uu____6632, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6637 -> aux l tl1)
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
        let uu____6684 = b  in
        match uu____6684 with
        | (x,aq) ->
            let uu____6693 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6693
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6707 =
                       let uu____6708 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6708  in
                     FStar_Parser_AST.mk_binder uu____6707 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6709 ->
                     let uu____6710 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6710
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6715 =
                          let uu____6716 =
                            let uu____6721 = bv_as_unique_ident x  in
                            (uu____6721, e)  in
                          FStar_Parser_AST.Annotated uu____6716  in
                        FStar_Parser_AST.mk_binder uu____6715 r
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
              let uu____6741 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6741  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6745 =
                if used
                then
                  let uu____6747 =
                    let uu____6754 = bv_as_unique_ident v1  in
                    (uu____6754, aqual)  in
                  FStar_Parser_AST.PatVar uu____6747
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6745  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6761;
                  FStar_Syntax_Syntax.vars = uu____6762;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6772 = FStar_Options.print_bound_var_types ()  in
                if uu____6772
                then
                  let uu____6775 =
                    let uu____6776 =
                      let uu____6787 =
                        let uu____6794 = resugar_term' env typ  in
                        (uu____6794, FStar_Pervasives_Native.None)  in
                      (pat, uu____6787)  in
                    FStar_Parser_AST.PatAscribed uu____6776  in
                  mk1 uu____6775
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
          let uu____6815 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6815
            (fun aqual  ->
               let uu____6827 =
                 let uu____6832 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6843  -> FStar_Pervasives_Native.Some _6843)
                   uu____6832
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6827)

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
          (let uu____6905 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6905) &&
            (let uu____6908 =
               FStar_List.existsML
                 (fun uu____6921  ->
                    match uu____6921 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6943)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6948 -> false
                          | uu____6950 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6908)
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
            let uu____7018 = may_drop_implicits args  in
            if uu____7018 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7043  ->
                 match uu____7043 with
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
              ((let uu____7098 =
                  let uu____7100 =
                    let uu____7102 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7102  in
                  Prims.op_Negation uu____7100  in
                if uu____7098
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
              let uu____7146 = filter_pattern_imp args  in
              (match uu____7146 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7196 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7196 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7215 =
                       let uu____7221 =
                         let uu____7223 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7223
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7221)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7215);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7276  ->
                        match uu____7276 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7293 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7293)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7301;
                 FStar_Syntax_Syntax.fv_delta = uu____7302;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7331 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7331 FStar_List.rev  in
              let args1 =
                let uu____7347 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7367  ->
                          match uu____7367 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7347 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7445 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7445
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7468 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7468
                 in
              let args2 =
                let uu____7486 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7486 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7530 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7530 with
               | FStar_Pervasives_Native.Some (op,uu____7542) ->
                   let uu____7559 =
                     let uu____7560 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7560  in
                   mk1 uu____7559
               | FStar_Pervasives_Native.None  ->
                   let uu____7570 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7570 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7575 ->
              let uu____7576 =
                let uu____7577 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7577  in
              mk1 uu____7576
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
          let uu____7617 =
            let uu____7620 =
              let uu____7621 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7621  in
            FStar_Pervasives_Native.Some uu____7620  in
          FStar_Pervasives_Native.Some uu____7617

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
          let uu____7633 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7633

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___7_7641  ->
    match uu___7_7641 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7648 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7649 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7650 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7655 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7664 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7673 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___8_7679  ->
    match uu___8_7679 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions  -> FStar_Parser_AST.PopOptions
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
            (tylid,uvs,bs,t,uu____7722,datacons) ->
            let uu____7732 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7760,uu____7761,uu____7762,inductive_lid,uu____7764,uu____7765)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7772 -> failwith "unexpected"))
               in
            (match uu____7732 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7793 = FStar_Options.print_implicits ()  in
                   if uu____7793 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7810 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___9_7817  ->
                             match uu___9_7817 with
                             | FStar_Syntax_Syntax.RecordType uu____7819 ->
                                 true
                             | uu____7829 -> false))
                      in
                   if uu____7810
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7883,univs1,term,uu____7886,num,uu____7888)
                           ->
                           let uu____7895 =
                             let uu____7896 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7896.FStar_Syntax_Syntax.n  in
                           (match uu____7895 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7910)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7979  ->
                                          match uu____7979 with
                                          | (b,qual) ->
                                              let uu____8000 =
                                                bv_as_unique_ident b  in
                                              let uu____8001 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8000, uu____8001,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8012 -> failwith "unexpected")
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
                            (l,univs1,term,uu____8155,num,uu____8157) ->
                            let c =
                              let uu____8178 =
                                let uu____8181 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8181  in
                              ((l.FStar_Ident.ident), uu____8178,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____8201 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8281 ->
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
        let uu____8307 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8307;
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
        let uu____8337 = ts  in
        match uu____8337 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8350 =
              let uu____8351 =
                let uu____8368 =
                  let uu____8377 =
                    let uu____8384 =
                      let uu____8385 =
                        let uu____8398 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8398)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8385  in
                    (uu____8384, FStar_Pervasives_Native.None)  in
                  [uu____8377]  in
                (false, false, uu____8368)  in
              FStar_Parser_AST.Tycon uu____8351  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8350
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tscheme" ts 
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun for_free  ->
      fun r  ->
        fun q  ->
          fun ed  ->
            let resugar_action d for_free1 =
              let action_params =
                FStar_Syntax_Subst.open_binders
                  d.FStar_Syntax_Syntax.action_params
                 in
              let uu____8487 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____8487 with
              | (bs,action_defn) ->
                  let uu____8494 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____8494 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____8504 = FStar_Options.print_implicits ()
                            in
                         if uu____8504
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____8514 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____8514 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____8531 =
                             let uu____8542 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____8542,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____8531  in
                         let t =
                           FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un
                            in
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
            let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident
               in
            let uu____8626 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____8626 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____8636 = FStar_Options.print_implicits ()  in
                  if uu____8636 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____8646 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____8646 FStar_List.rev  in
                let eff_typ1 = resugar_term' env eff_typ  in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.bind_wp
                   in
                let if_then_else1 =
                  resugar_tscheme'' env "if_then_else"
                    ed.FStar_Syntax_Syntax.if_then_else
                   in
                let ite_wp =
                  resugar_tscheme'' env "ite_wp"
                    ed.FStar_Syntax_Syntax.ite_wp
                   in
                let stronger =
                  resugar_tscheme'' env "stronger"
                    ed.FStar_Syntax_Syntax.stronger
                   in
                let close_wp =
                  resugar_tscheme'' env "close_wp"
                    ed.FStar_Syntax_Syntax.close_wp
                   in
                let assert_p =
                  resugar_tscheme'' env "assert_p"
                    ed.FStar_Syntax_Syntax.assert_p
                   in
                let assume_p =
                  resugar_tscheme'' env "assume_p"
                    ed.FStar_Syntax_Syntax.assume_p
                   in
                let null_wp =
                  resugar_tscheme'' env "null_wp"
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial
                   in
                let repr =
                  resugar_tscheme'' env "repr"
                    ([], (ed.FStar_Syntax_Syntax.repr))
                   in
                let return_repr =
                  resugar_tscheme'' env "return_repr"
                    ed.FStar_Syntax_Syntax.return_repr
                   in
                let bind_repr =
                  resugar_tscheme'' env "bind_repr"
                    ed.FStar_Syntax_Syntax.bind_repr
                   in
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
                    trivial]
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8731) ->
          let uu____8740 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8763 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8781 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8789 -> false
                    | uu____8806 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8740 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8844 se1 =
                 match uu____8844 with
                 | (datacon_ses1,tycons) ->
                     let uu____8870 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8870 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8885 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8885 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8920 =
                           let uu____8921 =
                             let uu____8922 =
                               let uu____8939 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____8939)  in
                             FStar_Parser_AST.Tycon uu____8922  in
                           decl'_to_decl se uu____8921  in
                         FStar_Pervasives_Native.Some uu____8920
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8974,uu____8975,uu____8976,uu____8977,uu____8978)
                              ->
                              let uu____8985 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8985
                          | uu____8988 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8992 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8999) ->
          let uu____9004 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9012  ->
                    match uu___10_9012 with
                    | FStar_Syntax_Syntax.Projector (uu____9014,uu____9015)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9017 -> true
                    | uu____9019 -> false))
             in
          if uu____9004
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9054) ->
                 let uu____9083 =
                   let uu____9084 =
                     let uu____9085 =
                       let uu____9096 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9096)  in
                     FStar_Parser_AST.TopLevelLet uu____9085  in
                   decl'_to_decl se uu____9084  in
                 FStar_Pervasives_Native.Some uu____9083
             | uu____9133 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9138,fml) ->
          let uu____9140 =
            let uu____9141 =
              let uu____9142 =
                let uu____9147 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9147)  in
              FStar_Parser_AST.Assume uu____9142  in
            decl'_to_decl se uu____9141  in
          FStar_Pervasives_Native.Some uu____9140
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9149 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9149
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____9152 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9152
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9162,t) ->
                let uu____9172 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9172
            | uu____9173 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9181,t) ->
                let uu____9191 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9191
            | uu____9192 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9216 -> failwith "Should not happen hopefully"  in
          let uu____9226 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9226
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9236 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9236 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9248 = FStar_Options.print_implicits ()  in
                 if uu____9248 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9264 =
                 let uu____9265 =
                   let uu____9266 =
                     let uu____9283 =
                       let uu____9292 =
                         let uu____9299 =
                           let uu____9300 =
                             let uu____9313 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9313)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9300  in
                         (uu____9299, FStar_Pervasives_Native.None)  in
                       [uu____9292]  in
                     (false, false, uu____9283)  in
                   FStar_Parser_AST.Tycon uu____9266  in
                 decl'_to_decl se uu____9265  in
               FStar_Pervasives_Native.Some uu____9264)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9345 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9345
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9349 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___11_9357  ->
                    match uu___11_9357 with
                    | FStar_Syntax_Syntax.Projector (uu____9359,uu____9360)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9362 -> true
                    | uu____9364 -> false))
             in
          if uu____9349
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9372 =
                 (let uu____9376 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9376) || (FStar_List.isEmpty uvs)
                  in
               if uu____9372
               then resugar_term' env t
               else
                 (let uu____9381 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9381 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9390 = resugar_term' env t1  in
                      label universes uu____9390)
                in
             let uu____9391 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9391)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9398 =
            let uu____9399 =
              let uu____9400 =
                let uu____9407 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9412 = resugar_term' env t  in
                (uu____9407, uu____9412)  in
              FStar_Parser_AST.Splice uu____9400  in
            decl'_to_decl se uu____9399  in
          FStar_Pervasives_Native.Some uu____9398
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9415 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9432 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9448 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9472 = noenv resugar_term'  in uu____9472 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9490 = noenv resugar_sigelt'  in uu____9490 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9508 = noenv resugar_comp'  in uu____9508 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9531 = noenv resugar_pat'  in uu____9531 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9565 = noenv resugar_binder'  in uu____9565 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9590 = noenv resugar_tscheme'  in uu____9590 ts 
let (resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____9625 = noenv resugar_eff_decl'  in
          uu____9625 for_free r q ed
  