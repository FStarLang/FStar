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
               (FStar_Syntax_Syntax.Meta
               (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____143,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____144)) -> false
            | (uu____149,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____150)) -> false
            | uu____154 -> true))
  
let filter_pattern_imp :
  'Auu____167 .
    ('Auu____167 * Prims.bool) Prims.list ->
      ('Auu____167 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____202  ->
         match uu____202 with
         | (uu____209,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____259 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____272 = FStar_Options.print_universes ()  in
    if uu____272
    then
      let uu____276 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____276 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____325 ->
          let uu____326 = universe_to_int Prims.int_zero u  in
          (match uu____326 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____337 =
                      let uu____338 =
                        let uu____339 =
                          let uu____351 = FStar_Util.string_of_int n1  in
                          (uu____351, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____339  in
                      FStar_Parser_AST.Const uu____338  in
                    mk1 uu____337 r
                | uu____364 ->
                    let e1 =
                      let uu____366 =
                        let uu____367 =
                          let uu____368 =
                            let uu____380 = FStar_Util.string_of_int n1  in
                            (uu____380, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____368  in
                        FStar_Parser_AST.Const uu____367  in
                      mk1 uu____366 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____394 =
                      let uu____395 =
                        let uu____402 = FStar_Ident.id_of_text "+"  in
                        (uu____402, [e1; e2])  in
                      FStar_Parser_AST.Op uu____395  in
                    mk1 uu____394 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____410 ->
               let t =
                 let uu____414 =
                   let uu____415 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____415  in
                 mk1 uu____414 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____424 =
                        let uu____425 =
                          let uu____432 = resugar_universe x r  in
                          (acc, uu____432, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____425  in
                      mk1 uu____424 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____434 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____446 =
              let uu____452 =
                let uu____454 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____454  in
              (uu____452, r)  in
            FStar_Ident.mk_ident uu____446  in
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
    let name_of_op uu___1_508 =
      match uu___1_508 with
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
      | uu____836 -> FStar_Pervasives_Native.None  in
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
    | uu____976 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____994 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____994 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1012 ->
               let maybeop =
                 let uu____1020 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1086)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1020
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
      let uu____1418 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1418 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1488 ->
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
                (let uu____1590 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1590
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1626 =
      let uu____1627 = FStar_Syntax_Subst.compress t  in
      uu____1627.FStar_Syntax_Syntax.n  in
    match uu____1626 with
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
        let uu____1648 = string_to_op s  in
        (match uu____1648 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1688 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1705 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1722 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1733 -> true
    | uu____1735 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1756 ->
        let uu____1758 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1758
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1772 = may_shorten lid  in
      if uu____1772 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1917 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1917  in
      let uu____1920 =
        let uu____1921 = FStar_Syntax_Subst.compress t  in
        uu____1921.FStar_Syntax_Syntax.n  in
      match uu____1920 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1924 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1941 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1941
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1944 =
              let uu____1947 = bv_as_unique_ident x  in [uu____1947]  in
            FStar_Ident.lid_of_ids uu____1944  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1950 =
              let uu____1953 = bv_as_unique_ident x  in [uu____1953]  in
            FStar_Ident.lid_of_ids uu____1950  in
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
            let uu____1972 =
              let uu____1973 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1973  in
            mk1 uu____1972
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
               | uu____1997 -> failwith "wrong projector format")
            else
              (let uu____2004 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2004
               then
                 let uu____2007 =
                   let uu____2008 =
                     let uu____2009 =
                       let uu____2015 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2015)  in
                     FStar_Ident.mk_ident uu____2009  in
                   FStar_Parser_AST.Tvar uu____2008  in
                 mk1 uu____2007
               else
                 (let uu____2020 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2020
                  then
                    let uu____2023 =
                      let uu____2024 =
                        let uu____2025 =
                          let uu____2031 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2031)  in
                        FStar_Ident.mk_ident uu____2025  in
                      FStar_Parser_AST.Tvar uu____2024  in
                    mk1 uu____2023
                  else
                    (let uu____2036 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2040 =
                            let uu____2042 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2042  in
                          let uu____2045 = FStar_String.get s Prims.int_zero
                             in
                          uu____2040 <> uu____2045)
                        in
                     if uu____2036
                     then
                       let uu____2050 =
                         let uu____2051 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2051  in
                       mk1 uu____2050
                     else
                       (let uu____2054 =
                          let uu____2055 =
                            let uu____2066 = maybe_shorten_fv env fv  in
                            (uu____2066, [])  in
                          FStar_Parser_AST.Construct uu____2055  in
                        mk1 uu____2054))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2084 = FStar_Options.print_universes ()  in
          if uu____2084
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
                   let uu____2115 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2115  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2138 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2146 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2146
          then
            let uu____2149 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2149
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2154 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2175 -> ("Type", true)  in
          (match uu____2154 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2187 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2187  in
               let uu____2188 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2188
               then
                 let uu____2191 =
                   let uu____2192 =
                     let uu____2199 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2199, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2192  in
                 mk1 uu____2191
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2204) ->
          let uu____2229 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2229 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2245 = FStar_Options.print_implicits ()  in
                 if uu____2245 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2283  ->
                         match uu____2283 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2323 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2323 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2333 = FStar_Options.print_implicits ()  in
                 if uu____2333 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2344 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2344 FStar_List.rev  in
               let rec aux body3 uu___2_2369 =
                 match uu___2_2369 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2385 =
            let uu____2390 =
              let uu____2391 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2391]  in
            FStar_Syntax_Subst.open_term uu____2390 phi  in
          (match uu____2385 with
           | (x1,phi1) ->
               let b =
                 let uu____2413 =
                   let uu____2416 = FStar_List.hd x1  in
                   resugar_binder' env uu____2416 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2413  in
               let uu____2423 =
                 let uu____2424 =
                   let uu____2429 = resugar_term' env phi1  in
                   (b, uu____2429)  in
                 FStar_Parser_AST.Refine uu____2424  in
               mk1 uu____2423)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2431;
             FStar_Syntax_Syntax.vars = uu____2432;_},(e,uu____2434)::[])
          when
          (let uu____2475 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2475) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2524 =
            match uu___3_2524 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2594 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2680,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2681))::tl1 ->
                  drop_implicits tl1
              | uu____2700 -> args2  in
            let uu____2709 = drop_implicits args1  in
            match uu____2709 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2741::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2771 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2871  ->
                   match uu____2871 with
                   | (e2,qual) ->
                       let uu____2888 = resugar_term' env e2  in
                       let uu____2889 = resugar_imp env qual  in
                       (uu____2888, uu____2889)) args1
               in
            let uu____2890 = resugar_term' env e1  in
            match uu____2890 with
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
                     fun uu____2927  ->
                       match uu____2927 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2943 = FStar_Options.print_implicits ()  in
            if uu____2943 then args else filter_imp args  in
          let uu____2958 = resugar_term_as_op e  in
          (match uu____2958 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2971) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2996  ->
                        match uu____2996 with
                        | (x,uu____3008) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____3017 =
                                   let uu____3018 =
                                     let uu____3019 =
                                       let uu____3026 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3026, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____3019  in
                                   mk1 uu____3018  in
                                 FStar_Pervasives_Native.Some uu____3017))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3030) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____3056)::[] -> b
                 | uu____3073 -> failwith "wrong arguments to dtuple"  in
               let uu____3083 =
                 let uu____3084 = FStar_Syntax_Subst.compress body  in
                 uu____3084.FStar_Syntax_Syntax.n  in
               (match uu____3083 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3089) ->
                    let uu____3114 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3114 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3124 = FStar_Options.print_implicits ()
                              in
                           if uu____3124 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3141 =
                           let uu____3142 =
                             let uu____3153 =
                               FStar_List.map
                                 (fun _3164  -> FStar_Util.Inl _3164) xs3
                                in
                             (uu____3153, body3)  in
                           FStar_Parser_AST.Sum uu____3142  in
                         mk1 uu____3141)
                | uu____3171 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3194  ->
                              match uu____3194 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3212) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3221) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3230 = FStar_List.hd args1  in
               (match uu____3230 with
                | (t1,uu____3244) ->
                    let uu____3249 =
                      let uu____3250 = FStar_Syntax_Subst.compress t1  in
                      uu____3250.FStar_Syntax_Syntax.n  in
                    (match uu____3249 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3257 =
                           let uu____3258 =
                             let uu____3263 = resugar_term' env t1  in
                             (uu____3263, f)  in
                           FStar_Parser_AST.Project uu____3258  in
                         mk1 uu____3257
                     | uu____3264 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3265) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___427_3292  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3302 =
                           match new_args with
                           | (a1,uu____3312)::(a2,uu____3314)::[] -> (a1, a2)
                           | uu____3341 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3302 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3363 =
                                  let uu____3364 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3364.FStar_Syntax_Syntax.n  in
                                match uu____3363 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3369) ->
                                    let uu____3394 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3394 with | (x1,e2) -> e2)
                                | uu____3401 ->
                                    let uu____3402 =
                                      let uu____3404 =
                                        let uu____3406 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3406
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3404
                                       in
                                    failwith uu____3402
                                 in
                              let body1 =
                                let uu____3409 = decomp body  in
                                resugar_term' env uu____3409  in
                              let handler1 =
                                let uu____3411 = decomp handler  in
                                resugar_term' env uu____3411  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3419,uu____3420,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3452,uu____3453,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3490 =
                                      let uu____3491 =
                                        let uu____3500 = resugar_body t11  in
                                        (uu____3500, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3491
                                       in
                                    mk1 uu____3490
                                | uu____3503 ->
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
                                | uu____3561 -> []  in
                              let branches = resugar_branches handler1  in
                              mk1 (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3594 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3595) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3604) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3627) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3692,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3724,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3755 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3768 =
                   let uu____3769 = FStar_Syntax_Subst.compress body  in
                   uu____3769.FStar_Syntax_Syntax.n  in
                 match uu____3768 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3774) ->
                     let uu____3799 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3799 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3809 = FStar_Options.print_implicits ()
                               in
                            if uu____3809 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3825 =
                            let uu____3834 =
                              let uu____3835 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3835.FStar_Syntax_Syntax.n  in
                            match uu____3834 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3853 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3870,pats) ->
                                      let uu____3904 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3948  ->
                                                     match uu____3948 with
                                                     | (e2,uu____3956) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3904, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3972 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3972)
                                  | uu____3981 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3853 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4013 ->
                                let uu____4014 = resugar_term' env body2  in
                                ([], uu____4014)
                             in
                          (match uu____3825 with
                           | (pats,body3) ->
                               let uu____4031 = uncurry xs3 pats body3  in
                               (match uu____4031 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4062 =
                                        let uu____4063 =
                                          let uu____4082 =
                                            let uu____4093 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4093, pats1)  in
                                          (xs4, uu____4082, body4)  in
                                        FStar_Parser_AST.QForall uu____4063
                                         in
                                      mk1 uu____4062
                                    else
                                      (let uu____4116 =
                                         let uu____4117 =
                                           let uu____4136 =
                                             let uu____4147 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4147, pats1)  in
                                           (xs4, uu____4136, body4)  in
                                         FStar_Parser_AST.QExists uu____4117
                                          in
                                       mk1 uu____4116))))
                 | uu____4168 ->
                     if op = "forall"
                     then
                       let uu____4172 =
                         let uu____4173 =
                           let uu____4192 = resugar_term' env body  in
                           ([], ([], []), uu____4192)  in
                         FStar_Parser_AST.QForall uu____4173  in
                       mk1 uu____4172
                     else
                       (let uu____4215 =
                          let uu____4216 =
                            let uu____4235 = resugar_term' env body  in
                            ([], ([], []), uu____4235)  in
                          FStar_Parser_AST.QExists uu____4216  in
                        mk1 uu____4215)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4274)::[] -> resugar_forall_body b
                  | uu____4291 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4303) ->
               let uu____4311 = FStar_List.hd args1  in
               (match uu____4311 with
                | (e1,uu____4325) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4397  ->
                         match uu____4397 with
                         | (e1,qual) ->
                             let uu____4414 = resugar_term' env e1  in
                             let uu____4415 = resugar_imp env qual  in
                             (uu____4414, uu____4415)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4431 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4431 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4479 =
                               let uu____4480 =
                                 let uu____4487 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4487)  in
                               FStar_Parser_AST.Op uu____4480  in
                             mk1 uu____4479  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4505  ->
                                  match uu____4505 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4524 =
                      let uu____4525 =
                        let uu____4532 =
                          let uu____4535 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4535
                           in
                        (op1, uu____4532)  in
                      FStar_Parser_AST.Op uu____4525  in
                    mk1 uu____4524
                | uu____4548 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4617 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4617 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4663 =
                   let uu____4676 =
                     let uu____4681 = resugar_pat' env pat1 branch_bv  in
                     let uu____4682 = resugar_term' env e  in
                     (uu____4681, uu____4682)  in
                   (FStar_Pervasives_Native.None, uu____4676)  in
                 [uu____4663]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4734,t1)::(pat2,uu____4737,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4833 =
            let uu____4834 =
              let uu____4841 = resugar_term' env e  in
              let uu____4842 = resugar_term' env t1  in
              let uu____4843 = resugar_term' env t2  in
              (uu____4841, uu____4842, uu____4843)  in
            FStar_Parser_AST.If uu____4834  in
          mk1 uu____4833
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4909 =
            match uu____4909 with
            | (pat,wopt,b) ->
                let uu____4951 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4951 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5003 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5003
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5007 =
            let uu____5008 =
              let uu____5023 = resugar_term' env e  in
              let uu____5024 = FStar_List.map resugar_branch branches  in
              (uu____5023, uu____5024)  in
            FStar_Parser_AST.Match uu____5008  in
          mk1 uu____5007
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5070) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5139 =
            let uu____5140 =
              let uu____5149 = resugar_term' env e  in
              (uu____5149, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5140  in
          mk1 uu____5139
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5178 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5178 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5232 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5232
                    in
                 let uu____5239 =
                   let uu____5244 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5244
                    in
                 match uu____5239 with
                 | (univs1,td) ->
                     let uu____5264 =
                       let uu____5271 =
                         let uu____5272 = FStar_Syntax_Subst.compress td  in
                         uu____5272.FStar_Syntax_Syntax.n  in
                       match uu____5271 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5281,(t1,uu____5283)::(d,uu____5285)::[])
                           -> (t1, d)
                       | uu____5342 -> failwith "wrong let binding format"
                        in
                     (match uu____5264 with
                      | (typ,def) ->
                          let uu____5373 =
                            let uu____5389 =
                              let uu____5390 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5390.FStar_Syntax_Syntax.n  in
                            match uu____5389 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5410) ->
                                let uu____5435 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5435 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5466 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5466
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5489 -> ([], def, false)  in
                          (match uu____5373 with
                           | (binders,term,is_pat_app) ->
                               let uu____5544 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5555 =
                                       let uu____5556 =
                                         let uu____5557 =
                                           let uu____5564 =
                                             bv_as_unique_ident bv  in
                                           (uu____5564,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5557
                                          in
                                       mk_pat uu____5556  in
                                     (uu____5555, term)
                                  in
                               (match uu____5544 with
                                | (pat,term1) ->
                                    let uu____5586 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5629  ->
                                                  match uu____5629 with
                                                  | (bv,q) ->
                                                      let uu____5644 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5644
                                                        (fun q1  ->
                                                           let uu____5656 =
                                                             let uu____5657 =
                                                               let uu____5664
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5664,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5657
                                                              in
                                                           mk_pat uu____5656)))
                                           in
                                        let uu____5667 =
                                          let uu____5672 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5672)
                                           in
                                        let uu____5675 =
                                          universe_to_string univs1  in
                                        (uu____5667, uu____5675)
                                      else
                                        (let uu____5684 =
                                           let uu____5689 =
                                             resugar_term' env term1  in
                                           (pat, uu____5689)  in
                                         let uu____5690 =
                                           universe_to_string univs1  in
                                         (uu____5684, uu____5690))
                                       in
                                    (attrs_opt, uu____5586))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5796 =
                   match uu____5796 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5856 =
                         let uu____5858 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5858  in
                       if uu____5856
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5939) ->
          let s =
            let uu____5958 =
              let uu____5960 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5960 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5958  in
          let uu____5965 = mk1 FStar_Parser_AST.Wild  in label s uu____5965
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5973 =
            let uu____5974 =
              let uu____5979 = resugar_term' env tm  in (uu____5979, qi1)  in
            FStar_Parser_AST.Quote uu____5974  in
          mk1 uu____5973
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_5991 =
            match uu___4_5991 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5999,(uu____6000,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6061 =
                        let uu____6062 =
                          let uu____6071 = resugar_seq t11  in
                          (uu____6071, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6062  in
                      mk1 uu____6061
                  | uu____6074 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6075,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6139  ->
                         match uu____6139 with
                         | (x,uu____6147) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6152 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6163,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6169,uu____6170,t1)
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
               let uu____6210 = FStar_Options.print_universes ()  in
               if uu____6210
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
               let uu____6274 = FStar_Options.print_universes ()  in
               if uu____6274
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
            let uu____6318 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6318, FStar_Parser_AST.Nothing)  in
          let uu____6319 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6319
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6342 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6342
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6427 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6427, (FStar_Pervasives_Native.snd post))  in
                    let uu____6438 =
                      let uu____6447 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6447 then [] else [pre]  in
                    let uu____6482 =
                      let uu____6491 =
                        let uu____6500 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6500 then [] else [pats]  in
                      FStar_List.append [post1] uu____6491  in
                    FStar_List.append uu____6438 uu____6482
                | uu____6559 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6593  ->
                   match uu____6593 with
                   | (e,uu____6605) ->
                       let uu____6610 = resugar_term' env e  in
                       (uu____6610, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6635 =
              match uu___5_6635 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6668 = resugar_term' env e  in
                         (uu____6668, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6673 -> aux l tl1)
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
        let uu____6720 = b  in
        match uu____6720 with
        | (x,aq) ->
            let uu____6729 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6729
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6743 =
                       let uu____6744 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6744  in
                     FStar_Parser_AST.mk_binder uu____6743 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6745 ->
                     let uu____6746 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6746
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6751 =
                          let uu____6752 =
                            let uu____6757 = bv_as_unique_ident x  in
                            (uu____6757, e)  in
                          FStar_Parser_AST.Annotated uu____6752  in
                        FStar_Parser_AST.mk_binder uu____6751 r
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
              let uu____6777 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6777  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6781 =
                if used
                then
                  let uu____6783 =
                    let uu____6790 = bv_as_unique_ident v1  in
                    (uu____6790, aqual)  in
                  FStar_Parser_AST.PatVar uu____6783
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6781  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6797;
                  FStar_Syntax_Syntax.vars = uu____6798;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6808 = FStar_Options.print_bound_var_types ()  in
                if uu____6808
                then
                  let uu____6811 =
                    let uu____6812 =
                      let uu____6823 =
                        let uu____6830 = resugar_term' env typ  in
                        (uu____6830, FStar_Pervasives_Native.None)  in
                      (pat, uu____6823)  in
                    FStar_Parser_AST.PatAscribed uu____6812  in
                  mk1 uu____6811
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
          let uu____6851 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6851
            (fun aqual  ->
               let uu____6863 =
                 let uu____6868 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6879  -> FStar_Pervasives_Native.Some _6879)
                   uu____6868
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6863)

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
          (let uu____6941 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6941) &&
            (let uu____6944 =
               FStar_List.existsML
                 (fun uu____6957  ->
                    match uu____6957 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6979)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6984 -> false
                          | uu____6986 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6944)
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
            let uu____7054 = may_drop_implicits args  in
            if uu____7054 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7079  ->
                 match uu____7079 with
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
              ((let uu____7134 =
                  let uu____7136 =
                    let uu____7138 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7138  in
                  Prims.op_Negation uu____7136  in
                if uu____7134
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
              let uu____7182 = filter_pattern_imp args  in
              (match uu____7182 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7232 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7232 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7251 =
                       let uu____7257 =
                         let uu____7259 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7259
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7257)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7251);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7312  ->
                        match uu____7312 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7329 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7329)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7337;
                 FStar_Syntax_Syntax.fv_delta = uu____7338;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7367 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7367 FStar_List.rev  in
              let args1 =
                let uu____7383 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7403  ->
                          match uu____7403 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7383 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7481 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7481
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7504 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7504
                 in
              let args2 =
                let uu____7522 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7522 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7566 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7566 with
               | FStar_Pervasives_Native.Some (op,uu____7578) ->
                   let uu____7595 =
                     let uu____7596 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7596  in
                   mk1 uu____7595
               | FStar_Pervasives_Native.None  ->
                   let uu____7606 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7606 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7611 ->
              let uu____7612 =
                let uu____7613 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7613  in
              mk1 uu____7612
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
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____7653 =
            let uu____7656 =
              let uu____7657 =
                let uu____7658 = resugar_term' env t  in
                FStar_Parser_AST.Arg_qualifier_meta_tac uu____7658  in
              FStar_Parser_AST.Meta uu____7657  in
            FStar_Pervasives_Native.Some uu____7656  in
          FStar_Pervasives_Native.Some uu____7653
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____7664 =
            let uu____7667 =
              let uu____7668 =
                let uu____7669 = resugar_term' env t  in
                FStar_Parser_AST.Arg_qualifier_meta_attr uu____7669  in
              FStar_Parser_AST.Meta uu____7668  in
            FStar_Pervasives_Native.Some uu____7667  in
          FStar_Pervasives_Native.Some uu____7664

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
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____7681 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7681
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          FStar_Parser_AST.Nothing

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7692  ->
    match uu___6_7692 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7699 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7700 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7701 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7706 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7715 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7724 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7730  ->
    match uu___7_7730 with
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
            (tylid,uvs,bs,t,uu____7773,datacons) ->
            let uu____7783 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7811,uu____7812,uu____7813,inductive_lid,uu____7815,uu____7816)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7823 -> failwith "unexpected"))
               in
            (match uu____7783 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7844 = FStar_Options.print_implicits ()  in
                   if uu____7844 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7861 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7868  ->
                             match uu___8_7868 with
                             | FStar_Syntax_Syntax.RecordType uu____7870 ->
                                 true
                             | uu____7880 -> false))
                      in
                   if uu____7861
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7918,univs1,term,uu____7921,num,uu____7923)
                           ->
                           let uu____7930 =
                             let uu____7931 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7931.FStar_Syntax_Syntax.n  in
                           (match uu____7930 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7941)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7998  ->
                                          match uu____7998 with
                                          | (b,qual) ->
                                              let uu____8015 =
                                                bv_as_unique_ident b  in
                                              let uu____8016 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8015, uu____8016)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8021 -> failwith "unexpected")
                       | uu____8029 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____8124,num,uu____8126) ->
                            let c =
                              let uu____8143 =
                                let uu____8146 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8146  in
                              ((l.FStar_Ident.ident), uu____8143, false)  in
                            c :: constructors
                        | uu____8160 -> failwith "unexpected"  in
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
                let uu____8301 =
                  let uu____8304 =
                    let uu____8305 =
                      let uu____8318 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____8318)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____8305  in
                  [uu____8304]  in
                (false, false, uu____8301)  in
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
              let uu____8383 = resugar_tscheme'' env name ts  in [uu____8383]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8401 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8403 =
             let uu____8406 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8408 =
               let uu____8411 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8413 =
                 let uu____8416 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8418 =
                   let uu____8421 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8423 =
                     let uu____8426 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8428 =
                       let uu____8431 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8431 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8426 :: uu____8428  in
                   uu____8421 :: uu____8423  in
                 uu____8416 :: uu____8418  in
               uu____8411 :: uu____8413  in
             uu____8406 :: uu____8408  in
           uu____8401 :: uu____8403)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8461 =
        match uu____8461 with
        | (ts,uu____8468) -> resugar_tscheme'' env name ts  in
      let uu____8469 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8471 =
        let uu____8474 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8476 =
          let uu____8479 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8481 =
            let uu____8484 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8486 =
              let uu____8489 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8489]  in
            uu____8484 :: uu____8486  in
          uu____8479 :: uu____8481  in
        uu____8474 :: uu____8476  in
      uu____8469 :: uu____8471
  
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
            let uu____8550 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8550 with
            | (bs,action_defn) ->
                let uu____8557 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8557 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8567 = FStar_Options.print_implicits ()  in
                       if uu____8567
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8577 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8577 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8594 =
                           let uu____8605 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8605,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8594  in
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
          let uu____8649 =
            let uu____8654 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8654
             in
          match uu____8649 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8672 = FStar_Options.print_implicits ()  in
                if uu____8672 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8682 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8682 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8732) ->
          let uu____8741 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8764 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8782 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8790 -> false
                    | uu____8807 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8741 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8845 se1 =
                 match uu____8845 with
                 | (datacon_ses1,tycons) ->
                     let uu____8871 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8871 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8886 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8886 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8921 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____8921
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8932,uu____8933,uu____8934,uu____8935,uu____8936)
                              ->
                              let uu____8943 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8943
                          | uu____8946 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8950 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____8956 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8970) ->
          let uu____8975 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_8983  ->
                    match uu___9_8983 with
                    | FStar_Syntax_Syntax.Projector (uu____8985,uu____8986)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8988 -> true
                    | uu____8990 -> false))
             in
          if uu____8975
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9025) ->
                 let uu____9054 =
                   let uu____9055 =
                     let uu____9056 =
                       let uu____9067 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9067)  in
                     FStar_Parser_AST.TopLevelLet uu____9056  in
                   decl'_to_decl se uu____9055  in
                 FStar_Pervasives_Native.Some uu____9054
             | uu____9104 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9109,fml) ->
          let uu____9111 =
            let uu____9112 =
              let uu____9113 =
                let uu____9118 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9118)  in
              FStar_Parser_AST.Assume uu____9113  in
            decl'_to_decl se uu____9112  in
          FStar_Pervasives_Native.Some uu____9111
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9120 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9120
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9129,t) ->
                let uu____9139 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9139
            | uu____9140 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9148,t) ->
                let uu____9158 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9158
            | uu____9159 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9183 -> failwith "Should not happen hopefully"  in
          let uu____9193 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9193
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9203 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9203 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9215 = FStar_Options.print_implicits ()  in
                 if uu____9215 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9231 =
                 let uu____9232 =
                   let uu____9233 =
                     let uu____9244 =
                       let uu____9247 =
                         let uu____9248 =
                           let uu____9261 = resugar_comp' env c1  in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____9261)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____9248  in
                       [uu____9247]  in
                     (false, false, uu____9244)  in
                   FStar_Parser_AST.Tycon uu____9233  in
                 decl'_to_decl se uu____9232  in
               FStar_Pervasives_Native.Some uu____9231)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9273 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9273
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9277 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9285  ->
                    match uu___10_9285 with
                    | FStar_Syntax_Syntax.Projector (uu____9287,uu____9288)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9290 -> true
                    | uu____9292 -> false))
             in
          if uu____9277
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9300 =
                 (let uu____9304 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9304) || (FStar_List.isEmpty uvs)
                  in
               if uu____9300
               then resugar_term' env t
               else
                 (let uu____9309 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9309 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9318 = resugar_term' env t1  in
                      label universes uu____9318)
                in
             let uu____9319 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9319)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9326 =
            let uu____9327 =
              let uu____9328 =
                let uu____9335 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9340 = resugar_term' env t  in
                (uu____9335, uu____9340)  in
              FStar_Parser_AST.Splice uu____9328  in
            decl'_to_decl se uu____9327  in
          FStar_Pervasives_Native.Some uu____9326
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9343 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9360 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9376 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n1,p,(uu____9380,t),uu____9382) ->
          let uu____9391 =
            let uu____9392 =
              let uu____9393 =
                let uu____9402 = resugar_term' env t  in
                (m, n1, p, uu____9402)  in
              FStar_Parser_AST.Polymonadic_bind uu____9393  in
            decl'_to_decl se uu____9392  in
          FStar_Pervasives_Native.Some uu____9391
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9426 = noenv resugar_term'  in uu____9426 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9444 = noenv resugar_sigelt'  in uu____9444 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9462 = noenv resugar_comp'  in uu____9462 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9485 = noenv resugar_pat'  in uu____9485 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9519 = noenv resugar_binder'  in uu____9519 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9544 = noenv resugar_tscheme'  in uu____9544 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9572 = noenv resugar_eff_decl'  in uu____9572 r q ed
  