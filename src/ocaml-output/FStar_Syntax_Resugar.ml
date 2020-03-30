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
          let uu____1943 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1943
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1946 =
              let uu____1949 = bv_as_unique_ident x  in [uu____1949]  in
            FStar_Ident.lid_of_ids uu____1946  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1952 =
              let uu____1955 = bv_as_unique_ident x  in [uu____1955]  in
            FStar_Ident.lid_of_ids uu____1952  in
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
            let uu____1974 =
              let uu____1975 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1975  in
            mk1 uu____1974
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
               | uu____1999 -> failwith "wrong projector format")
            else
              (let uu____2006 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2006
               then
                 let uu____2009 =
                   let uu____2010 =
                     let uu____2011 =
                       let uu____2017 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2017)  in
                     FStar_Ident.mk_ident uu____2011  in
                   FStar_Parser_AST.Tvar uu____2010  in
                 mk1 uu____2009
               else
                 (let uu____2022 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2022
                  then
                    let uu____2025 =
                      let uu____2026 =
                        let uu____2027 =
                          let uu____2033 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2033)  in
                        FStar_Ident.mk_ident uu____2027  in
                      FStar_Parser_AST.Tvar uu____2026  in
                    mk1 uu____2025
                  else
                    (let uu____2038 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2042 =
                            let uu____2044 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2044  in
                          let uu____2047 = FStar_String.get s Prims.int_zero
                             in
                          uu____2042 <> uu____2047)
                        in
                     if uu____2038
                     then
                       let uu____2052 =
                         let uu____2053 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2053  in
                       mk1 uu____2052
                     else
                       (let uu____2056 =
                          let uu____2057 =
                            let uu____2068 = maybe_shorten_fv env fv  in
                            (uu____2068, [])  in
                          FStar_Parser_AST.Construct uu____2057  in
                        mk1 uu____2056))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2086 = FStar_Options.print_universes ()  in
          if uu____2086
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
                   let uu____2117 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2117  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2140 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2148 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2148
          then
            let uu____2151 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2151
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2156 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2177 -> ("Type", true)  in
          (match uu____2156 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2189 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2189  in
               let uu____2190 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2190
               then
                 let uu____2193 =
                   let uu____2194 =
                     let uu____2201 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2201, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2194  in
                 mk1 uu____2193
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2206) ->
          let uu____2231 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2231 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2247 = FStar_Options.print_implicits ()  in
                 if uu____2247 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2285  ->
                         match uu____2285 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2325 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2325 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2335 = FStar_Options.print_implicits ()  in
                 if uu____2335 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2346 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2346 FStar_List.rev  in
               let rec aux body3 uu___2_2371 =
                 match uu___2_2371 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2387 =
            let uu____2392 =
              let uu____2393 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2393]  in
            FStar_Syntax_Subst.open_term uu____2392 phi  in
          (match uu____2387 with
           | (x1,phi1) ->
               let b =
                 let uu____2415 =
                   let uu____2418 = FStar_List.hd x1  in
                   resugar_binder' env uu____2418 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2415  in
               let uu____2425 =
                 let uu____2426 =
                   let uu____2431 = resugar_term' env phi1  in
                   (b, uu____2431)  in
                 FStar_Parser_AST.Refine uu____2426  in
               mk1 uu____2425)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2433;
             FStar_Syntax_Syntax.vars = uu____2434;_},(e,uu____2436)::[])
          when
          (let uu____2477 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2477) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2526 =
            match uu___3_2526 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2596 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2682,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2683))::tl1 ->
                  drop_implicits tl1
              | uu____2702 -> args2  in
            let uu____2711 = drop_implicits args1  in
            match uu____2711 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2743::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2773 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2873  ->
                   match uu____2873 with
                   | (e2,qual) ->
                       let uu____2890 = resugar_term' env e2  in
                       let uu____2891 = resugar_imp env qual  in
                       (uu____2890, uu____2891)) args1
               in
            let uu____2892 = resugar_term' env e1  in
            match uu____2892 with
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
                     fun uu____2929  ->
                       match uu____2929 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2945 = FStar_Options.print_implicits ()  in
            if uu____2945 then args else filter_imp args  in
          let uu____2960 = resugar_term_as_op e  in
          (match uu____2960 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2973) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2998  ->
                        match uu____2998 with
                        | (x,uu____3010) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____3019 =
                                   let uu____3020 =
                                     let uu____3021 =
                                       let uu____3028 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3028, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____3021  in
                                   mk1 uu____3020  in
                                 FStar_Pervasives_Native.Some uu____3019))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3032) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____3058)::[] -> b
                 | uu____3075 -> failwith "wrong arguments to dtuple"  in
               let uu____3085 =
                 let uu____3086 = FStar_Syntax_Subst.compress body  in
                 uu____3086.FStar_Syntax_Syntax.n  in
               (match uu____3085 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3091) ->
                    let uu____3116 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3116 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3126 = FStar_Options.print_implicits ()
                              in
                           if uu____3126 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3143 =
                           let uu____3144 =
                             let uu____3155 =
                               FStar_List.map
                                 (fun _3166  -> FStar_Util.Inl _3166) xs3
                                in
                             (uu____3155, body3)  in
                           FStar_Parser_AST.Sum uu____3144  in
                         mk1 uu____3143)
                | uu____3173 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3196  ->
                              match uu____3196 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3214) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3223) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3232 = FStar_List.hd args1  in
               (match uu____3232 with
                | (t1,uu____3246) ->
                    let uu____3251 =
                      let uu____3252 = FStar_Syntax_Subst.compress t1  in
                      uu____3252.FStar_Syntax_Syntax.n  in
                    (match uu____3251 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3259 =
                           let uu____3260 =
                             let uu____3265 = resugar_term' env t1  in
                             (uu____3265, f)  in
                           FStar_Parser_AST.Project uu____3260  in
                         mk1 uu____3259
                     | uu____3266 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3267) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___426_3294  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3304 =
                           match new_args with
                           | (a1,uu____3314)::(a2,uu____3316)::[] -> (a1, a2)
                           | uu____3343 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3304 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3365 =
                                  let uu____3366 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3366.FStar_Syntax_Syntax.n  in
                                match uu____3365 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3371) ->
                                    let uu____3396 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3396 with | (x1,e2) -> e2)
                                | uu____3403 ->
                                    let uu____3404 =
                                      let uu____3406 =
                                        let uu____3408 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3408
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3406
                                       in
                                    failwith uu____3404
                                 in
                              let body1 =
                                let uu____3411 = decomp body  in
                                resugar_term' env uu____3411  in
                              let handler1 =
                                let uu____3413 = decomp handler  in
                                resugar_term' env uu____3413  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3421,uu____3422,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3454,uu____3455,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3492 =
                                      let uu____3493 =
                                        let uu____3502 = resugar_body t11  in
                                        (uu____3502, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3493
                                       in
                                    mk1 uu____3492
                                | uu____3505 ->
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
                                | uu____3563 -> []  in
                              let branches = resugar_branches handler1  in
                              mk1 (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3596 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3597) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3606) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3629) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3694,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3726,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3757 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3770 =
                   let uu____3771 = FStar_Syntax_Subst.compress body  in
                   uu____3771.FStar_Syntax_Syntax.n  in
                 match uu____3770 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3776) ->
                     let uu____3801 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3801 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3811 = FStar_Options.print_implicits ()
                               in
                            if uu____3811 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3827 =
                            let uu____3836 =
                              let uu____3837 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3837.FStar_Syntax_Syntax.n  in
                            match uu____3836 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3855 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3872,pats) ->
                                      let uu____3906 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3950  ->
                                                     match uu____3950 with
                                                     | (e2,uu____3958) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3906, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3974 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3974)
                                  | uu____3983 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3855 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4015 ->
                                let uu____4016 = resugar_term' env body2  in
                                ([], uu____4016)
                             in
                          (match uu____3827 with
                           | (pats,body3) ->
                               let uu____4033 = uncurry xs3 pats body3  in
                               (match uu____4033 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4064 =
                                        let uu____4065 =
                                          let uu____4084 =
                                            let uu____4095 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4095, pats1)  in
                                          (xs4, uu____4084, body4)  in
                                        FStar_Parser_AST.QForall uu____4065
                                         in
                                      mk1 uu____4064
                                    else
                                      (let uu____4118 =
                                         let uu____4119 =
                                           let uu____4138 =
                                             let uu____4149 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4149, pats1)  in
                                           (xs4, uu____4138, body4)  in
                                         FStar_Parser_AST.QExists uu____4119
                                          in
                                       mk1 uu____4118))))
                 | uu____4170 ->
                     if op = "forall"
                     then
                       let uu____4174 =
                         let uu____4175 =
                           let uu____4194 = resugar_term' env body  in
                           ([], ([], []), uu____4194)  in
                         FStar_Parser_AST.QForall uu____4175  in
                       mk1 uu____4174
                     else
                       (let uu____4217 =
                          let uu____4218 =
                            let uu____4237 = resugar_term' env body  in
                            ([], ([], []), uu____4237)  in
                          FStar_Parser_AST.QExists uu____4218  in
                        mk1 uu____4217)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4276)::[] -> resugar_forall_body b
                  | uu____4293 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4305) ->
               let uu____4313 = FStar_List.hd args1  in
               (match uu____4313 with
                | (e1,uu____4327) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4399  ->
                         match uu____4399 with
                         | (e1,qual) ->
                             let uu____4416 = resugar_term' env e1  in
                             let uu____4417 = resugar_imp env qual  in
                             (uu____4416, uu____4417)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4433 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4433 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4481 =
                               let uu____4482 =
                                 let uu____4489 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4489)  in
                               FStar_Parser_AST.Op uu____4482  in
                             mk1 uu____4481  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4507  ->
                                  match uu____4507 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4526 =
                      let uu____4527 =
                        let uu____4534 =
                          let uu____4537 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4537
                           in
                        (op1, uu____4534)  in
                      FStar_Parser_AST.Op uu____4527  in
                    mk1 uu____4526
                | uu____4550 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4619 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4619 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4665 =
                   let uu____4678 =
                     let uu____4683 = resugar_pat' env pat1 branch_bv  in
                     let uu____4684 = resugar_term' env e  in
                     (uu____4683, uu____4684)  in
                   (FStar_Pervasives_Native.None, uu____4678)  in
                 [uu____4665]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4736,t1)::(pat2,uu____4739,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4835 =
            let uu____4836 =
              let uu____4843 = resugar_term' env e  in
              let uu____4844 = resugar_term' env t1  in
              let uu____4845 = resugar_term' env t2  in
              (uu____4843, uu____4844, uu____4845)  in
            FStar_Parser_AST.If uu____4836  in
          mk1 uu____4835
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4911 =
            match uu____4911 with
            | (pat,wopt,b) ->
                let uu____4953 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4953 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5005 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5005
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5009 =
            let uu____5010 =
              let uu____5025 = resugar_term' env e  in
              let uu____5026 = FStar_List.map resugar_branch branches  in
              (uu____5025, uu____5026)  in
            FStar_Parser_AST.Match uu____5010  in
          mk1 uu____5009
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5072) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5141 =
            let uu____5142 =
              let uu____5151 = resugar_term' env e  in
              (uu____5151, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5142  in
          mk1 uu____5141
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5180 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5180 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5234 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5234
                    in
                 let uu____5241 =
                   let uu____5246 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5246
                    in
                 match uu____5241 with
                 | (univs1,td) ->
                     let uu____5266 =
                       let uu____5273 =
                         let uu____5274 = FStar_Syntax_Subst.compress td  in
                         uu____5274.FStar_Syntax_Syntax.n  in
                       match uu____5273 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5283,(t1,uu____5285)::(d,uu____5287)::[])
                           -> (t1, d)
                       | uu____5344 -> failwith "wrong let binding format"
                        in
                     (match uu____5266 with
                      | (typ,def) ->
                          let uu____5375 =
                            let uu____5391 =
                              let uu____5392 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5392.FStar_Syntax_Syntax.n  in
                            match uu____5391 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5412) ->
                                let uu____5437 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5437 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5468 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5468
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5491 -> ([], def, false)  in
                          (match uu____5375 with
                           | (binders,term,is_pat_app) ->
                               let uu____5546 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5557 =
                                       let uu____5558 =
                                         let uu____5559 =
                                           let uu____5566 =
                                             bv_as_unique_ident bv  in
                                           (uu____5566,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5559
                                          in
                                       mk_pat uu____5558  in
                                     (uu____5557, term)
                                  in
                               (match uu____5546 with
                                | (pat,term1) ->
                                    let uu____5588 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5631  ->
                                                  match uu____5631 with
                                                  | (bv,q) ->
                                                      let uu____5646 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5646
                                                        (fun q1  ->
                                                           let uu____5658 =
                                                             let uu____5659 =
                                                               let uu____5666
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5666,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5659
                                                              in
                                                           mk_pat uu____5658)))
                                           in
                                        let uu____5669 =
                                          let uu____5674 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5674)
                                           in
                                        let uu____5677 =
                                          universe_to_string univs1  in
                                        (uu____5669, uu____5677)
                                      else
                                        (let uu____5686 =
                                           let uu____5691 =
                                             resugar_term' env term1  in
                                           (pat, uu____5691)  in
                                         let uu____5692 =
                                           universe_to_string univs1  in
                                         (uu____5686, uu____5692))
                                       in
                                    (attrs_opt, uu____5588))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5798 =
                   match uu____5798 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5858 =
                         let uu____5860 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5860  in
                       if uu____5858
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5941) ->
          let s =
            let uu____5960 =
              let uu____5962 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5962 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5960  in
          let uu____5967 = mk1 FStar_Parser_AST.Wild  in label s uu____5967
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5975 =
            let uu____5976 =
              let uu____5981 = resugar_term' env tm  in (uu____5981, qi1)  in
            FStar_Parser_AST.Quote uu____5976  in
          mk1 uu____5975
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_5993 =
            match uu___4_5993 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6001,(uu____6002,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6063 =
                        let uu____6064 =
                          let uu____6073 = resugar_seq t11  in
                          (uu____6073, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6064  in
                      mk1 uu____6063
                  | uu____6076 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6077,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6141  ->
                         match uu____6141 with
                         | (x,uu____6149) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6154 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6165,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6171,uu____6172,t1)
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
               let uu____6212 = FStar_Options.print_universes ()  in
               if uu____6212
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
               let uu____6276 = FStar_Options.print_universes ()  in
               if uu____6276
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
            let uu____6320 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6320, FStar_Parser_AST.Nothing)  in
          let uu____6321 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6321
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6344 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6344
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6429 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6429, (FStar_Pervasives_Native.snd post))  in
                    let uu____6440 =
                      let uu____6449 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6449 then [] else [pre]  in
                    let uu____6484 =
                      let uu____6493 =
                        let uu____6502 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6502 then [] else [pats]  in
                      FStar_List.append [post1] uu____6493  in
                    FStar_List.append uu____6440 uu____6484
                | uu____6561 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6595  ->
                   match uu____6595 with
                   | (e,uu____6607) ->
                       let uu____6612 = resugar_term' env e  in
                       (uu____6612, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6637 =
              match uu___5_6637 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6670 = resugar_term' env e  in
                         (uu____6670, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6675 -> aux l tl1)
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
        let uu____6722 = b  in
        match uu____6722 with
        | (x,aq) ->
            let uu____6731 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6731
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6745 =
                       let uu____6746 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6746  in
                     FStar_Parser_AST.mk_binder uu____6745 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6747 ->
                     let uu____6748 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6748
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6753 =
                          let uu____6754 =
                            let uu____6759 = bv_as_unique_ident x  in
                            (uu____6759, e)  in
                          FStar_Parser_AST.Annotated uu____6754  in
                        FStar_Parser_AST.mk_binder uu____6753 r
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
              let uu____6779 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6779  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6783 =
                if used
                then
                  let uu____6785 =
                    let uu____6792 = bv_as_unique_ident v1  in
                    (uu____6792, aqual)  in
                  FStar_Parser_AST.PatVar uu____6785
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6783  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6799;
                  FStar_Syntax_Syntax.vars = uu____6800;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6810 = FStar_Options.print_bound_var_types ()  in
                if uu____6810
                then
                  let uu____6813 =
                    let uu____6814 =
                      let uu____6825 =
                        let uu____6832 = resugar_term' env typ  in
                        (uu____6832, FStar_Pervasives_Native.None)  in
                      (pat, uu____6825)  in
                    FStar_Parser_AST.PatAscribed uu____6814  in
                  mk1 uu____6813
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
          let uu____6853 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6853
            (fun aqual  ->
               let uu____6865 =
                 let uu____6870 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6881  -> FStar_Pervasives_Native.Some _6881)
                   uu____6870
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6865)

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
          (let uu____6943 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6943) &&
            (let uu____6946 =
               FStar_List.existsML
                 (fun uu____6959  ->
                    match uu____6959 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6981)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6986 -> false
                          | uu____6988 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6946)
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
            let uu____7056 = may_drop_implicits args  in
            if uu____7056 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7081  ->
                 match uu____7081 with
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
              ((let uu____7136 =
                  let uu____7138 =
                    let uu____7140 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7140  in
                  Prims.op_Negation uu____7138  in
                if uu____7136
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
              let uu____7184 = filter_pattern_imp args  in
              (match uu____7184 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7234 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7234 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7253 =
                       let uu____7259 =
                         let uu____7261 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7261
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7259)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7253);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7314  ->
                        match uu____7314 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7331 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7331)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7339;
                 FStar_Syntax_Syntax.fv_delta = uu____7340;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7369 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7369 FStar_List.rev  in
              let args1 =
                let uu____7385 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7405  ->
                          match uu____7405 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7385 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7483 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7483
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7506 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7506
                 in
              let args2 =
                let uu____7524 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7524 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7568 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7568 with
               | FStar_Pervasives_Native.Some (op,uu____7580) ->
                   let uu____7597 =
                     let uu____7598 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7598  in
                   mk1 uu____7597
               | FStar_Pervasives_Native.None  ->
                   let uu____7608 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7608 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7613 ->
              let uu____7614 =
                let uu____7615 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7615  in
              mk1 uu____7614
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
          let uu____7655 =
            let uu____7658 =
              let uu____7659 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7659  in
            FStar_Pervasives_Native.Some uu____7658  in
          FStar_Pervasives_Native.Some uu____7655

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
          let uu____7671 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7671

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7679  ->
    match uu___6_7679 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7686 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7687 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7688 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7693 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7702 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7711 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7717  ->
    match uu___7_7717 with
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
            (tylid,uvs,bs,t,uu____7760,datacons) ->
            let uu____7770 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7798,uu____7799,uu____7800,inductive_lid,uu____7802,uu____7803)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7810 -> failwith "unexpected"))
               in
            (match uu____7770 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7831 = FStar_Options.print_implicits ()  in
                   if uu____7831 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7848 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7855  ->
                             match uu___8_7855 with
                             | FStar_Syntax_Syntax.RecordType uu____7857 ->
                                 true
                             | uu____7867 -> false))
                      in
                   if uu____7848
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7905,univs1,term,uu____7908,num,uu____7910)
                           ->
                           let uu____7917 =
                             let uu____7918 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7918.FStar_Syntax_Syntax.n  in
                           (match uu____7917 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7928)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7985  ->
                                          match uu____7985 with
                                          | (b,qual) ->
                                              let uu____8002 =
                                                bv_as_unique_ident b  in
                                              let uu____8003 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8002, uu____8003)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8008 -> failwith "unexpected")
                       | uu____8016 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____8111,num,uu____8113) ->
                            let c =
                              let uu____8130 =
                                let uu____8133 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8133  in
                              ((l.FStar_Ident.ident), uu____8130, false)  in
                            c :: constructors
                        | uu____8147 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8207 ->
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
        let uu____8233 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8233;
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
        let uu____8263 = ts  in
        match uu____8263 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8276 =
              let uu____8277 =
                let uu____8288 =
                  let uu____8291 =
                    let uu____8292 =
                      let uu____8305 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____8305)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____8292  in
                  [uu____8291]  in
                (false, false, uu____8288)  in
              FStar_Parser_AST.Tycon uu____8277  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8276
  
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
              let uu____8370 = resugar_tscheme'' env name ts  in [uu____8370]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8388 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8390 =
             let uu____8393 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8395 =
               let uu____8398 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8400 =
                 let uu____8403 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8405 =
                   let uu____8408 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8410 =
                     let uu____8413 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8415 =
                       let uu____8418 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8418 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8413 :: uu____8415  in
                   uu____8408 :: uu____8410  in
                 uu____8403 :: uu____8405  in
               uu____8398 :: uu____8400  in
             uu____8393 :: uu____8395  in
           uu____8388 :: uu____8390)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8448 =
        match uu____8448 with
        | (ts,uu____8455) -> resugar_tscheme'' env name ts  in
      let uu____8456 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8458 =
        let uu____8461 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8463 =
          let uu____8466 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8468 =
            let uu____8471 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8473 =
              let uu____8476 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8476]  in
            uu____8471 :: uu____8473  in
          uu____8466 :: uu____8468  in
        uu____8461 :: uu____8463  in
      uu____8456 :: uu____8458
  
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
            let uu____8537 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8537 with
            | (bs,action_defn) ->
                let uu____8544 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8544 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8554 = FStar_Options.print_implicits ()  in
                       if uu____8554
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8564 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8564 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8581 =
                           let uu____8592 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8592,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8581  in
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
          let uu____8636 =
            let uu____8641 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8641
             in
          match uu____8636 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8659 = FStar_Options.print_implicits ()  in
                if uu____8659 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8669 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8669 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8719) ->
          let uu____8728 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8751 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8769 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8777 -> false
                    | uu____8794 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8728 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8832 se1 =
                 match uu____8832 with
                 | (datacon_ses1,tycons) ->
                     let uu____8858 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8858 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8873 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8873 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8908 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____8908
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8919,uu____8920,uu____8921,uu____8922,uu____8923)
                              ->
                              let uu____8930 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8930
                          | uu____8933 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8937 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____8943 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8957) ->
          let uu____8962 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_8970  ->
                    match uu___9_8970 with
                    | FStar_Syntax_Syntax.Projector (uu____8972,uu____8973)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8975 -> true
                    | uu____8977 -> false))
             in
          if uu____8962
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9012) ->
                 let uu____9041 =
                   let uu____9042 =
                     let uu____9043 =
                       let uu____9054 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9054)  in
                     FStar_Parser_AST.TopLevelLet uu____9043  in
                   decl'_to_decl se uu____9042  in
                 FStar_Pervasives_Native.Some uu____9041
             | uu____9091 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9096,fml) ->
          let uu____9098 =
            let uu____9099 =
              let uu____9100 =
                let uu____9105 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9105)  in
              FStar_Parser_AST.Assume uu____9100  in
            decl'_to_decl se uu____9099  in
          FStar_Pervasives_Native.Some uu____9098
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9107 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9107
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9116,t) ->
                let uu____9126 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9126
            | uu____9127 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9135,t) ->
                let uu____9145 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9145
            | uu____9146 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9170 -> failwith "Should not happen hopefully"  in
          let uu____9180 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9180
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9190 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9190 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9202 = FStar_Options.print_implicits ()  in
                 if uu____9202 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9218 =
                 let uu____9219 =
                   let uu____9220 =
                     let uu____9231 =
                       let uu____9234 =
                         let uu____9235 =
                           let uu____9248 = resugar_comp' env c1  in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____9248)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____9235  in
                       [uu____9234]  in
                     (false, false, uu____9231)  in
                   FStar_Parser_AST.Tycon uu____9220  in
                 decl'_to_decl se uu____9219  in
               FStar_Pervasives_Native.Some uu____9218)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9260 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9260
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9264 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9272  ->
                    match uu___10_9272 with
                    | FStar_Syntax_Syntax.Projector (uu____9274,uu____9275)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9277 -> true
                    | uu____9279 -> false))
             in
          if uu____9264
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9287 =
                 (let uu____9291 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9291) || (FStar_List.isEmpty uvs)
                  in
               if uu____9287
               then resugar_term' env t
               else
                 (let uu____9296 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9296 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9305 = resugar_term' env t1  in
                      label universes uu____9305)
                in
             let uu____9306 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9306)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9313 =
            let uu____9314 =
              let uu____9315 =
                let uu____9322 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9327 = resugar_term' env t  in
                (uu____9322, uu____9327)  in
              FStar_Parser_AST.Splice uu____9315  in
            decl'_to_decl se uu____9314  in
          FStar_Pervasives_Native.Some uu____9313
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9330 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9347 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9363 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n1,p,(uu____9367,t),uu____9369) ->
          let uu____9378 =
            let uu____9379 =
              let uu____9380 =
                let uu____9389 = resugar_term' env t  in
                (m, n1, p, uu____9389)  in
              FStar_Parser_AST.Polymonadic_bind uu____9380  in
            decl'_to_decl se uu____9379  in
          FStar_Pervasives_Native.Some uu____9378
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9413 = noenv resugar_term'  in uu____9413 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9431 = noenv resugar_sigelt'  in uu____9431 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9449 = noenv resugar_comp'  in uu____9449 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9472 = noenv resugar_pat'  in uu____9472 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9506 = noenv resugar_binder'  in uu____9506 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9531 = noenv resugar_tscheme'  in uu____9531 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9559 = noenv resugar_eff_decl'  in uu____9559 r q ed
  