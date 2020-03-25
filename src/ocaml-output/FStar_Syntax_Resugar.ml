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
  = fun uu____51  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____60 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____60
      then
        let uu____64 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____64
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____74 .
    ('Auu____74 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____74 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_129  ->
            match uu___0_129 with
            | (uu____137,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____144,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____145)) -> false
            | (uu____150,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____151)) -> false
            | uu____157 -> true))
  
let filter_pattern_imp :
  'Auu____170 .
    ('Auu____170 * Prims.bool) Prims.list ->
      ('Auu____170 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____205  ->
         match uu____205 with
         | (uu____212,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____262 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____275 = FStar_Options.print_universes ()  in
    if uu____275
    then
      let uu____279 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____279 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____328 ->
          let uu____329 = universe_to_int Prims.int_zero u  in
          (match uu____329 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____340 =
                      let uu____341 =
                        let uu____342 =
                          let uu____354 = FStar_Util.string_of_int n1  in
                          (uu____354, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____342  in
                      FStar_Parser_AST.Const uu____341  in
                    mk1 uu____340 r
                | uu____367 ->
                    let e1 =
                      let uu____369 =
                        let uu____370 =
                          let uu____371 =
                            let uu____383 = FStar_Util.string_of_int n1  in
                            (uu____383, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____371  in
                        FStar_Parser_AST.Const uu____370  in
                      mk1 uu____369 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____397 =
                      let uu____398 =
                        let uu____405 = FStar_Ident.id_of_text "+"  in
                        (uu____405, [e1; e2])  in
                      FStar_Parser_AST.Op uu____398  in
                    mk1 uu____397 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____413 ->
               let t =
                 let uu____417 =
                   let uu____418 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____418  in
                 mk1 uu____417 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____427 =
                        let uu____428 =
                          let uu____435 = resugar_universe x r  in
                          (acc, uu____435, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____428  in
                      mk1 uu____427 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____437 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____449 =
              let uu____455 =
                let uu____457 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____457  in
              (uu____455, r)  in
            FStar_Ident.mk_ident uu____449  in
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
    let name_of_op uu___1_511 =
      match uu___1_511 with
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
      | uu____839 -> FStar_Pervasives_Native.None  in
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
    | uu____979 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____997 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____997 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1015 ->
               let maybeop =
                 let uu____1023 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1089)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1023
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
      let uu____1421 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1421 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1491 ->
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
                (let uu____1593 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1593
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1629 =
      let uu____1630 = FStar_Syntax_Subst.compress t  in
      uu____1630.FStar_Syntax_Syntax.n  in
    match uu____1629 with
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
        let uu____1651 = string_to_op s  in
        (match uu____1651 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1691 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1708 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1725 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1736 -> true
    | uu____1738 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1759 ->
        let uu____1761 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1761
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1775 = may_shorten lid  in
      if uu____1775 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1920 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1920  in
      let uu____1923 =
        let uu____1924 = FStar_Syntax_Subst.compress t  in
        uu____1924.FStar_Syntax_Syntax.n  in
      match uu____1923 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1927 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1952 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1952
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1955 =
              let uu____1958 = bv_as_unique_ident x  in [uu____1958]  in
            FStar_Ident.lid_of_ids uu____1955  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1961 =
              let uu____1964 = bv_as_unique_ident x  in [uu____1964]  in
            FStar_Ident.lid_of_ids uu____1961  in
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
            let uu____1983 =
              let uu____1984 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1984  in
            mk1 uu____1983
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
               | uu____2008 -> failwith "wrong projector format")
            else
              (let uu____2015 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2015
               then
                 let uu____2018 =
                   let uu____2019 =
                     let uu____2020 =
                       let uu____2026 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2026)  in
                     FStar_Ident.mk_ident uu____2020  in
                   FStar_Parser_AST.Tvar uu____2019  in
                 mk1 uu____2018
               else
                 (let uu____2031 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2031
                  then
                    let uu____2034 =
                      let uu____2035 =
                        let uu____2036 =
                          let uu____2042 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2042)  in
                        FStar_Ident.mk_ident uu____2036  in
                      FStar_Parser_AST.Tvar uu____2035  in
                    mk1 uu____2034
                  else
                    (let uu____2047 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2051 =
                            let uu____2053 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2053  in
                          let uu____2056 = FStar_String.get s Prims.int_zero
                             in
                          uu____2051 <> uu____2056)
                        in
                     if uu____2047
                     then
                       let uu____2061 =
                         let uu____2062 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2062  in
                       mk1 uu____2061
                     else
                       (let uu____2065 =
                          let uu____2066 =
                            let uu____2077 = maybe_shorten_fv env fv  in
                            (uu____2077, [])  in
                          FStar_Parser_AST.Construct uu____2066  in
                        mk1 uu____2065))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2095 = FStar_Options.print_universes ()  in
          if uu____2095
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
                   let uu____2126 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2126  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2149 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2157 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2157
          then
            let uu____2160 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2160
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2165 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2186 -> ("Type", true)  in
          (match uu____2165 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2198 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2198  in
               let uu____2199 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2199
               then
                 let uu____2202 =
                   let uu____2203 =
                     let uu____2210 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2210, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2203  in
                 mk1 uu____2202
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2215) ->
          let uu____2240 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2240 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2256 = FStar_Options.print_implicits ()  in
                 if uu____2256 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2294  ->
                         match uu____2294 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2334 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2334 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2344 = FStar_Options.print_implicits ()  in
                 if uu____2344 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2355 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2355 FStar_List.rev  in
               let rec aux body3 uu___2_2380 =
                 match uu___2_2380 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2396 =
            let uu____2401 =
              let uu____2402 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2402]  in
            FStar_Syntax_Subst.open_term uu____2401 phi  in
          (match uu____2396 with
           | (x1,phi1) ->
               let b =
                 let uu____2424 =
                   let uu____2427 = FStar_List.hd x1  in
                   resugar_binder' env uu____2427 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2424  in
               let uu____2434 =
                 let uu____2435 =
                   let uu____2440 = resugar_term' env phi1  in
                   (b, uu____2440)  in
                 FStar_Parser_AST.Refine uu____2435  in
               mk1 uu____2434)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2442;
             FStar_Syntax_Syntax.vars = uu____2443;_},(e,uu____2445)::[])
          when
          (let uu____2486 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2486) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2535 =
            match uu___3_2535 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2605 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2691,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2692))::tl1 ->
                  drop_implicits tl1
              | uu____2711 -> args2  in
            let uu____2720 = drop_implicits args1  in
            match uu____2720 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2752::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2782 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2882  ->
                   match uu____2882 with
                   | (e2,qual) ->
                       let uu____2899 = resugar_term' env e2  in
                       let uu____2900 = resugar_imp env qual  in
                       (uu____2899, uu____2900)) args1
               in
            let uu____2901 = resugar_term' env e1  in
            match uu____2901 with
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
                     fun uu____2938  ->
                       match uu____2938 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2954 = FStar_Options.print_implicits ()  in
            if uu____2954 then args else filter_imp args  in
          let uu____2969 = resugar_term_as_op e  in
          (match uu____2969 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2982) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____3007  ->
                        match uu____3007 with
                        | (x,uu____3019) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____3028 =
                                   let uu____3029 =
                                     let uu____3030 =
                                       let uu____3037 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3037, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____3030  in
                                   mk1 uu____3029  in
                                 FStar_Pervasives_Native.Some uu____3028))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3041) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____3067)::[] -> b
                 | uu____3084 -> failwith "wrong arguments to dtuple"  in
               let uu____3094 =
                 let uu____3095 = FStar_Syntax_Subst.compress body  in
                 uu____3095.FStar_Syntax_Syntax.n  in
               (match uu____3094 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3100) ->
                    let uu____3125 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3125 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3135 = FStar_Options.print_implicits ()
                              in
                           if uu____3135 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3152 =
                           let uu____3153 =
                             let uu____3164 =
                               FStar_List.map
                                 (fun uu____3175  ->
                                    FStar_Util.Inl uu____3175) xs3
                                in
                             (uu____3164, body3)  in
                           FStar_Parser_AST.Sum uu____3153  in
                         mk1 uu____3152)
                | uu____3182 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3205  ->
                              match uu____3205 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3223) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3232) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3241 = FStar_List.hd args1  in
               (match uu____3241 with
                | (t1,uu____3255) ->
                    let uu____3260 =
                      let uu____3261 = FStar_Syntax_Subst.compress t1  in
                      uu____3261.FStar_Syntax_Syntax.n  in
                    (match uu____3260 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3268 =
                           let uu____3269 =
                             let uu____3274 = resugar_term' env t1  in
                             (uu____3274, f)  in
                           FStar_Parser_AST.Project uu____3269  in
                         mk1 uu____3268
                     | uu____3275 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3276) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___426_3303  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3313 =
                           match new_args with
                           | (a1,uu____3323)::(a2,uu____3325)::[] -> (a1, a2)
                           | uu____3352 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3313 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3374 =
                                  let uu____3375 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3375.FStar_Syntax_Syntax.n  in
                                match uu____3374 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3380) ->
                                    let uu____3405 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3405 with | (x1,e2) -> e2)
                                | uu____3412 ->
                                    let uu____3413 =
                                      let uu____3415 =
                                        let uu____3417 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3417
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3415
                                       in
                                    failwith uu____3413
                                 in
                              let body1 =
                                let uu____3420 = decomp body  in
                                resugar_term' env uu____3420  in
                              let handler1 =
                                let uu____3422 = decomp handler  in
                                resugar_term' env uu____3422  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3430,uu____3431,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3463,uu____3464,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3501 =
                                      let uu____3502 =
                                        let uu____3511 = resugar_body t11  in
                                        (uu____3511, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3502
                                       in
                                    mk1 uu____3501
                                | uu____3514 ->
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
                                | uu____3572 -> []  in
                              let branches = resugar_branches handler1  in
                              mk1 (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3605 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3606) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3615) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3638) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3703,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3735,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3766 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3779 =
                   let uu____3780 = FStar_Syntax_Subst.compress body  in
                   uu____3780.FStar_Syntax_Syntax.n  in
                 match uu____3779 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3785) ->
                     let uu____3810 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3810 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3820 = FStar_Options.print_implicits ()
                               in
                            if uu____3820 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3836 =
                            let uu____3845 =
                              let uu____3846 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3846.FStar_Syntax_Syntax.n  in
                            match uu____3845 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3864 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3881,pats) ->
                                      let uu____3915 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3959  ->
                                                     match uu____3959 with
                                                     | (e2,uu____3967) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3915, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3983 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3983)
                                  | uu____3992 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3864 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4024 ->
                                let uu____4025 = resugar_term' env body2  in
                                ([], uu____4025)
                             in
                          (match uu____3836 with
                           | (pats,body3) ->
                               let uu____4042 = uncurry xs3 pats body3  in
                               (match uu____4042 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4073 =
                                        let uu____4074 =
                                          let uu____4093 =
                                            let uu____4104 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4104, pats1)  in
                                          (xs4, uu____4093, body4)  in
                                        FStar_Parser_AST.QForall uu____4074
                                         in
                                      mk1 uu____4073
                                    else
                                      (let uu____4127 =
                                         let uu____4128 =
                                           let uu____4147 =
                                             let uu____4158 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4158, pats1)  in
                                           (xs4, uu____4147, body4)  in
                                         FStar_Parser_AST.QExists uu____4128
                                          in
                                       mk1 uu____4127))))
                 | uu____4179 ->
                     if op = "forall"
                     then
                       let uu____4183 =
                         let uu____4184 =
                           let uu____4203 = resugar_term' env body  in
                           ([], ([], []), uu____4203)  in
                         FStar_Parser_AST.QForall uu____4184  in
                       mk1 uu____4183
                     else
                       (let uu____4226 =
                          let uu____4227 =
                            let uu____4246 = resugar_term' env body  in
                            ([], ([], []), uu____4246)  in
                          FStar_Parser_AST.QExists uu____4227  in
                        mk1 uu____4226)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4285)::[] -> resugar_forall_body b
                  | uu____4302 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4314) ->
               let uu____4322 = FStar_List.hd args1  in
               (match uu____4322 with
                | (e1,uu____4336) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4408  ->
                         match uu____4408 with
                         | (e1,qual) ->
                             let uu____4425 = resugar_term' env e1  in
                             let uu____4426 = resugar_imp env qual  in
                             (uu____4425, uu____4426)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4442 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4442 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4490 =
                               let uu____4491 =
                                 let uu____4498 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4498)  in
                               FStar_Parser_AST.Op uu____4491  in
                             mk1 uu____4490  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4516  ->
                                  match uu____4516 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4535 =
                      let uu____4536 =
                        let uu____4543 =
                          let uu____4546 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4546
                           in
                        (op1, uu____4543)  in
                      FStar_Parser_AST.Op uu____4536  in
                    mk1 uu____4535
                | uu____4559 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4628 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4628 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4674 =
                   let uu____4687 =
                     let uu____4692 = resugar_pat' env pat1 branch_bv  in
                     let uu____4693 = resugar_term' env e  in
                     (uu____4692, uu____4693)  in
                   (FStar_Pervasives_Native.None, uu____4687)  in
                 [uu____4674]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4745,t1)::(pat2,uu____4748,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4844 =
            let uu____4845 =
              let uu____4852 = resugar_term' env e  in
              let uu____4853 = resugar_term' env t1  in
              let uu____4854 = resugar_term' env t2  in
              (uu____4852, uu____4853, uu____4854)  in
            FStar_Parser_AST.If uu____4845  in
          mk1 uu____4844
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4920 =
            match uu____4920 with
            | (pat,wopt,b) ->
                let uu____4962 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4962 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5014 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5014
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5018 =
            let uu____5019 =
              let uu____5034 = resugar_term' env e  in
              let uu____5035 = FStar_List.map resugar_branch branches  in
              (uu____5034, uu____5035)  in
            FStar_Parser_AST.Match uu____5019  in
          mk1 uu____5018
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5081) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5150 =
            let uu____5151 =
              let uu____5160 = resugar_term' env e  in
              (uu____5160, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5151  in
          mk1 uu____5150
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5189 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5189 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5243 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5243
                    in
                 let uu____5250 =
                   let uu____5255 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5255
                    in
                 match uu____5250 with
                 | (univs1,td) ->
                     let uu____5275 =
                       let uu____5282 =
                         let uu____5283 = FStar_Syntax_Subst.compress td  in
                         uu____5283.FStar_Syntax_Syntax.n  in
                       match uu____5282 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5292,(t1,uu____5294)::(d,uu____5296)::[])
                           -> (t1, d)
                       | uu____5353 -> failwith "wrong let binding format"
                        in
                     (match uu____5275 with
                      | (typ,def) ->
                          let uu____5384 =
                            let uu____5400 =
                              let uu____5401 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5401.FStar_Syntax_Syntax.n  in
                            match uu____5400 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5421) ->
                                let uu____5446 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5446 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5477 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5477
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5500 -> ([], def, false)  in
                          (match uu____5384 with
                           | (binders,term,is_pat_app) ->
                               let uu____5555 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5566 =
                                       let uu____5567 =
                                         let uu____5568 =
                                           let uu____5575 =
                                             bv_as_unique_ident bv  in
                                           (uu____5575,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5568
                                          in
                                       mk_pat uu____5567  in
                                     (uu____5566, term)
                                  in
                               (match uu____5555 with
                                | (pat,term1) ->
                                    let uu____5597 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5640  ->
                                                  match uu____5640 with
                                                  | (bv,q) ->
                                                      let uu____5655 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5655
                                                        (fun q1  ->
                                                           let uu____5667 =
                                                             let uu____5668 =
                                                               let uu____5675
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5675,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5668
                                                              in
                                                           mk_pat uu____5667)))
                                           in
                                        let uu____5678 =
                                          let uu____5683 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5683)
                                           in
                                        let uu____5686 =
                                          universe_to_string univs1  in
                                        (uu____5678, uu____5686)
                                      else
                                        (let uu____5695 =
                                           let uu____5700 =
                                             resugar_term' env term1  in
                                           (pat, uu____5700)  in
                                         let uu____5701 =
                                           universe_to_string univs1  in
                                         (uu____5695, uu____5701))
                                       in
                                    (attrs_opt, uu____5597))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5807 =
                   match uu____5807 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5867 =
                         let uu____5869 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5869  in
                       if uu____5867
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5950) ->
          let s =
            let uu____5969 =
              let uu____5971 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5971 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5969  in
          let uu____5976 = mk1 FStar_Parser_AST.Wild  in label s uu____5976
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5984 =
            let uu____5985 =
              let uu____5990 = resugar_term' env tm  in (uu____5990, qi1)  in
            FStar_Parser_AST.Quote uu____5985  in
          mk1 uu____5984
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_6002 =
            match uu___4_6002 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6010,(uu____6011,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6072 =
                        let uu____6073 =
                          let uu____6082 = resugar_seq t11  in
                          (uu____6082, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6073  in
                      mk1 uu____6072
                  | uu____6085 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6086,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6150  ->
                         match uu____6150 with
                         | (x,uu____6158) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6163 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6174,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6180,uu____6181,t1)
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
               let uu____6221 = FStar_Options.print_universes ()  in
               if uu____6221
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
               let uu____6285 = FStar_Options.print_universes ()  in
               if uu____6285
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
            let uu____6329 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6329, FStar_Parser_AST.Nothing)  in
          let uu____6330 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6330
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6353 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6353
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6438 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6438, (FStar_Pervasives_Native.snd post))  in
                    let uu____6449 =
                      let uu____6458 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6458 then [] else [pre]  in
                    let uu____6493 =
                      let uu____6502 =
                        let uu____6511 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6511 then [] else [pats]  in
                      FStar_List.append [post1] uu____6502  in
                    FStar_List.append uu____6449 uu____6493
                | uu____6570 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6604  ->
                   match uu____6604 with
                   | (e,uu____6616) ->
                       let uu____6621 = resugar_term' env e  in
                       (uu____6621, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6646 =
              match uu___5_6646 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6679 = resugar_term' env e  in
                         (uu____6679, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6684 -> aux l tl1)
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
        let uu____6731 = b  in
        match uu____6731 with
        | (x,aq) ->
            let uu____6740 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6740
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6754 =
                       let uu____6755 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6755  in
                     FStar_Parser_AST.mk_binder uu____6754 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6756 ->
                     let uu____6757 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6757
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6762 =
                          let uu____6763 =
                            let uu____6768 = bv_as_unique_ident x  in
                            (uu____6768, e)  in
                          FStar_Parser_AST.Annotated uu____6763  in
                        FStar_Parser_AST.mk_binder uu____6762 r
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
              let uu____6788 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6788  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6792 =
                if used
                then
                  let uu____6794 =
                    let uu____6801 = bv_as_unique_ident v1  in
                    (uu____6801, aqual)  in
                  FStar_Parser_AST.PatVar uu____6794
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6792  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6808;
                  FStar_Syntax_Syntax.vars = uu____6809;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6819 = FStar_Options.print_bound_var_types ()  in
                if uu____6819
                then
                  let uu____6822 =
                    let uu____6823 =
                      let uu____6834 =
                        let uu____6841 = resugar_term' env typ  in
                        (uu____6841, FStar_Pervasives_Native.None)  in
                      (pat, uu____6834)  in
                    FStar_Parser_AST.PatAscribed uu____6823  in
                  mk1 uu____6822
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
          let uu____6862 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6862
            (fun aqual  ->
               let uu____6874 =
                 let uu____6879 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun uu____6890  ->
                      FStar_Pervasives_Native.Some uu____6890) uu____6879
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6874)

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
          (let uu____6952 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6952) &&
            (let uu____6955 =
               FStar_List.existsML
                 (fun uu____6968  ->
                    match uu____6968 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6990)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6995 -> false
                          | uu____6997 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6955)
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
            let uu____7065 = may_drop_implicits args  in
            if uu____7065 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7090  ->
                 match uu____7090 with
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
              ((let uu____7145 =
                  let uu____7147 =
                    let uu____7149 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7149  in
                  Prims.op_Negation uu____7147  in
                if uu____7145
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
              let uu____7193 = filter_pattern_imp args  in
              (match uu____7193 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7243 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7243 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7262 =
                       let uu____7268 =
                         let uu____7270 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7270
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7268)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7262);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7323  ->
                        match uu____7323 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7340 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7340)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7348;
                 FStar_Syntax_Syntax.fv_delta = uu____7349;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7378 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7378 FStar_List.rev  in
              let args1 =
                let uu____7394 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7414  ->
                          match uu____7414 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7394 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7492 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7492
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7515 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7515
                 in
              let args2 =
                let uu____7533 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7533 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7577 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7577 with
               | FStar_Pervasives_Native.Some (op,uu____7589) ->
                   let uu____7606 =
                     let uu____7607 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7607  in
                   mk1 uu____7606
               | FStar_Pervasives_Native.None  ->
                   let uu____7617 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7617 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7622 ->
              let uu____7623 =
                let uu____7624 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7624  in
              mk1 uu____7623
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
          let uu____7664 =
            let uu____7667 =
              let uu____7668 = resugar_term' env t  in
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
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____7680 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7680

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7688  ->
    match uu___6_7688 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7695 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7696 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7697 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7702 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7711 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7720 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7726  ->
    match uu___7_7726 with
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
            (tylid,uvs,bs,t,uu____7769,datacons) ->
            let uu____7779 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7807,uu____7808,uu____7809,inductive_lid,uu____7811,uu____7812)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7819 -> failwith "unexpected"))
               in
            (match uu____7779 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7840 = FStar_Options.print_implicits ()  in
                   if uu____7840 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7857 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7864  ->
                             match uu___8_7864 with
                             | FStar_Syntax_Syntax.RecordType uu____7866 ->
                                 true
                             | uu____7876 -> false))
                      in
                   if uu____7857
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7914,univs1,term,uu____7917,num,uu____7919)
                           ->
                           let uu____7926 =
                             let uu____7927 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7927.FStar_Syntax_Syntax.n  in
                           (match uu____7926 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7937)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7994  ->
                                          match uu____7994 with
                                          | (b,qual) ->
                                              let uu____8011 =
                                                bv_as_unique_ident b  in
                                              let uu____8012 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8011, uu____8012)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8017 -> failwith "unexpected")
                       | uu____8025 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____8120,num,uu____8122) ->
                            let c =
                              let uu____8139 =
                                let uu____8142 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8142  in
                              ((l.FStar_Ident.ident), uu____8139, false)  in
                            c :: constructors
                        | uu____8156 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8216 ->
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
        let uu____8242 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8242;
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
        let uu____8272 = ts  in
        match uu____8272 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8285 =
              let uu____8286 =
                let uu____8297 =
                  let uu____8300 =
                    let uu____8301 =
                      let uu____8314 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____8314)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____8301  in
                  [uu____8300]  in
                (false, false, uu____8297)  in
              FStar_Parser_AST.Tycon uu____8286  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8285
  
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
              let uu____8379 = resugar_tscheme'' env name ts  in [uu____8379]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8397 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8399 =
             let uu____8402 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8404 =
               let uu____8407 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8409 =
                 let uu____8412 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8414 =
                   let uu____8417 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8419 =
                     let uu____8422 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8424 =
                       let uu____8427 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8427 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8422 :: uu____8424  in
                   uu____8417 :: uu____8419  in
                 uu____8412 :: uu____8414  in
               uu____8407 :: uu____8409  in
             uu____8402 :: uu____8404  in
           uu____8397 :: uu____8399)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8457 =
        match uu____8457 with
        | (ts,uu____8464) -> resugar_tscheme'' env name ts  in
      let uu____8465 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8467 =
        let uu____8470 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8472 =
          let uu____8475 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8477 =
            let uu____8480 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8482 =
              let uu____8485 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8485]  in
            uu____8480 :: uu____8482  in
          uu____8475 :: uu____8477  in
        uu____8470 :: uu____8472  in
      uu____8465 :: uu____8467
  
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
            let uu____8546 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8546 with
            | (bs,action_defn) ->
                let uu____8553 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8553 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8563 = FStar_Options.print_implicits ()  in
                       if uu____8563
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8573 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8573 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8590 =
                           let uu____8601 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8601,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8590  in
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
          let uu____8645 =
            let uu____8650 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8650
             in
          match uu____8645 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8668 = FStar_Options.print_implicits ()  in
                if uu____8668 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8678 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8678 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8728) ->
          let uu____8737 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8760 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8778 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8786 -> false
                    | uu____8803 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8737 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8841 se1 =
                 match uu____8841 with
                 | (datacon_ses1,tycons) ->
                     let uu____8867 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8867 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8882 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8882 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8917 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____8917
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8928,uu____8929,uu____8930,uu____8931,uu____8932)
                              ->
                              let uu____8939 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8939
                          | uu____8942 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8946 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____8952 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8966) ->
          let uu____8971 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_8979  ->
                    match uu___9_8979 with
                    | FStar_Syntax_Syntax.Projector (uu____8981,uu____8982)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8984 -> true
                    | uu____8986 -> false))
             in
          if uu____8971
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9021) ->
                 let uu____9050 =
                   let uu____9051 =
                     let uu____9052 =
                       let uu____9063 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9063)  in
                     FStar_Parser_AST.TopLevelLet uu____9052  in
                   decl'_to_decl se uu____9051  in
                 FStar_Pervasives_Native.Some uu____9050
             | uu____9100 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9105,fml) ->
          let uu____9107 =
            let uu____9108 =
              let uu____9109 =
                let uu____9114 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9114)  in
              FStar_Parser_AST.Assume uu____9109  in
            decl'_to_decl se uu____9108  in
          FStar_Pervasives_Native.Some uu____9107
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9116 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9116
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9125,t) ->
                let uu____9135 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9135
            | uu____9136 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9144,t) ->
                let uu____9154 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9154
            | uu____9155 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9179 -> failwith "Should not happen hopefully"  in
          let uu____9189 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9189
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9199 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9199 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9211 = FStar_Options.print_implicits ()  in
                 if uu____9211 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9227 =
                 let uu____9228 =
                   let uu____9229 =
                     let uu____9240 =
                       let uu____9243 =
                         let uu____9244 =
                           let uu____9257 = resugar_comp' env c1  in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____9257)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____9244  in
                       [uu____9243]  in
                     (false, false, uu____9240)  in
                   FStar_Parser_AST.Tycon uu____9229  in
                 decl'_to_decl se uu____9228  in
               FStar_Pervasives_Native.Some uu____9227)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9269 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9269
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9273 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9281  ->
                    match uu___10_9281 with
                    | FStar_Syntax_Syntax.Projector (uu____9283,uu____9284)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9286 -> true
                    | uu____9288 -> false))
             in
          if uu____9273
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9296 =
                 (let uu____9300 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9300) || (FStar_List.isEmpty uvs)
                  in
               if uu____9296
               then resugar_term' env t
               else
                 (let uu____9305 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9305 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9314 = resugar_term' env t1  in
                      label universes uu____9314)
                in
             let uu____9315 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9315)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9322 =
            let uu____9323 =
              let uu____9324 =
                let uu____9331 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9336 = resugar_term' env t  in
                (uu____9331, uu____9336)  in
              FStar_Parser_AST.Splice uu____9324  in
            decl'_to_decl se uu____9323  in
          FStar_Pervasives_Native.Some uu____9322
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9339 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9356 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9372 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n1,p,(uu____9376,t),uu____9378) ->
          let uu____9387 =
            let uu____9388 =
              let uu____9389 =
                let uu____9398 = resugar_term' env t  in
                (m, n1, p, uu____9398)  in
              FStar_Parser_AST.Polymonadic_bind uu____9389  in
            decl'_to_decl se uu____9388  in
          FStar_Pervasives_Native.Some uu____9387
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9422 = noenv resugar_term'  in uu____9422 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9440 = noenv resugar_sigelt'  in uu____9440 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9458 = noenv resugar_comp'  in uu____9458 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9481 = noenv resugar_pat'  in uu____9481 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9515 = noenv resugar_binder'  in uu____9515 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9540 = noenv resugar_tscheme'  in uu____9540 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9568 = noenv resugar_eff_decl'  in uu____9568 r q ed
  