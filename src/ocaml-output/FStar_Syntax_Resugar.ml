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
  'uuuuuu33 'uuuuuu34 .
    unit ->
      ('uuuuuu33 -> 'uuuuuu34 FStar_Pervasives_Native.option) ->
        'uuuuuu33 Prims.list -> 'uuuuuu34 Prims.list
  = fun uu____51  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____60 =
        (let uu____64 = FStar_Ident.text_of_id x.FStar_Syntax_Syntax.ppname
            in
         FStar_Util.starts_with FStar_Ident.reserved_prefix uu____64) ||
          (FStar_Options.print_real_names ())
         in
      if uu____60
      then
        let uu____68 = FStar_Ident.text_of_id x.FStar_Syntax_Syntax.ppname
           in
        let uu____70 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat uu____68 uu____70
      else FStar_Ident.text_of_id x.FStar_Syntax_Syntax.ppname  in
    let uu____74 =
      let uu____80 = FStar_Ident.range_of_id x.FStar_Syntax_Syntax.ppname  in
      (unique_name, uu____80)  in
    FStar_Ident.mk_ident uu____74
  
let filter_imp :
  'uuuuuu87 .
    ('uuuuuu87 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu87 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_142  ->
            match uu___0_142 with
            | (uu____150,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____157,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____158)) -> false
            | (uu____163,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____164)) -> false
            | uu____170 -> true))
  
let filter_pattern_imp :
  'uuuuuu183 .
    ('uuuuuu183 * Prims.bool) Prims.list ->
      ('uuuuuu183 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____218  ->
         match uu____218 with
         | (uu____225,is_implicit) -> Prims.op_Negation is_implicit) xs
  
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
  fun n  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n + Prims.int_one) u1
      | uu____275 -> (n, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs  ->
    let uu____288 = FStar_Options.print_universes ()  in
    if uu____288
    then
      let uu____292 =
        FStar_List.map (fun x  -> FStar_Ident.text_of_id x) univs  in
      FStar_All.pipe_right uu____292 (FStar_String.concat ", ")
    else ""
  
let rec (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u  ->
    fun r  ->
      let mk a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____341 ->
          let uu____342 = universe_to_int Prims.int_zero u  in
          (match uu____342 with
           | (n,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____353 =
                      let uu____354 =
                        let uu____355 =
                          let uu____367 = FStar_Util.string_of_int n  in
                          (uu____367, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____355  in
                      FStar_Parser_AST.Const uu____354  in
                    mk uu____353 r
                | uu____380 ->
                    let e1 =
                      let uu____382 =
                        let uu____383 =
                          let uu____384 =
                            let uu____396 = FStar_Util.string_of_int n  in
                            (uu____396, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____384  in
                        FStar_Parser_AST.Const uu____383  in
                      mk uu____382 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____410 =
                      let uu____411 =
                        let uu____418 = FStar_Ident.id_of_text "+"  in
                        (uu____418, [e1; e2])  in
                      FStar_Parser_AST.Op uu____411  in
                    mk uu____410 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____426 ->
               let t =
                 let uu____430 =
                   let uu____431 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____431  in
                 mk uu____430 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____440 =
                        let uu____441 =
                          let uu____448 = resugar_universe x r  in
                          (acc, uu____448, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____441  in
                      mk uu____440 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____450 -> mk FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____462 =
              let uu____468 =
                let uu____470 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____470  in
              (uu____468, r)  in
            FStar_Ident.mk_ident uu____462  in
          mk (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk FStar_Parser_AST.Wild r
  
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
    let name_of_op uu___1_524 =
      match uu___1_524 with
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
      | uu____852 -> FStar_Pervasives_Native.None  in
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
    | uu____992 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____1010 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____1010 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1028 ->
               let maybeop =
                 let uu____1036 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1102)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1036
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
      let uu____1434 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1434 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1504 ->
          let length =
            let uu____1513 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____1513  in
          let str =
            if length = Prims.int_zero
            then
              FStar_Ident.string_of_lid
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            else
              (let uu____1523 =
                 FStar_Ident.string_of_lid
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_Util.substring_from uu____1523 (length + Prims.int_one))
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
                (let uu____1610 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1610
                 then
                   let uu____1623 =
                     let uu____1632 =
                       FStar_Ident.string_of_lid
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     (uu____1632, FStar_Pervasives_Native.None)  in
                   FStar_Pervasives_Native.Some uu____1623
                 else FStar_Pervasives_Native.None)
       in
    let uu____1657 =
      let uu____1658 = FStar_Syntax_Subst.compress t  in
      uu____1658.FStar_Syntax_Syntax.n  in
    match uu____1657 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length =
          let uu____1670 =
            FStar_Ident.nsstr
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_String.length uu____1670  in
        let s =
          if length = Prims.int_zero
          then
            FStar_Ident.string_of_lid
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          else
            (let uu____1680 =
               FStar_Ident.string_of_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.substring_from uu____1680 (length + Prims.int_one))
           in
        let uu____1683 = string_to_op s  in
        (match uu____1683 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1723 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1740 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1757 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1768 -> true
    | uu____1770 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let uu____1786 = FStar_Ident.string_of_lid lid  in
    match uu____1786 with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1793 ->
        let uu____1795 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1795
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1809 = may_shorten lid  in
      if uu____1809 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____1954 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1954  in
      let uu____1957 =
        let uu____1958 = FStar_Syntax_Subst.compress t  in
        uu____1958.FStar_Syntax_Syntax.n  in
      match uu____1957 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1961 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1978 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1978
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1981 =
              let uu____1982 = bv_as_unique_ident x  in [uu____1982]  in
            FStar_Ident.lid_of_ids uu____1981  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1985 =
              let uu____1986 = bv_as_unique_ident x  in [uu____1986]  in
            FStar_Ident.lid_of_ids uu____1985  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length =
            let uu____1990 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____1990  in
          let s =
            if length = Prims.int_zero
            then FStar_Ident.string_of_lid a
            else
              (let uu____2000 = FStar_Ident.string_of_lid a  in
               FStar_Util.substring_from uu____2000 (length + Prims.int_one))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____2009 =
              let uu____2010 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____2010  in
            mk uu____2009
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
               | fst::snd::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst] t.FStar_Syntax_Syntax.pos
                      in
                   let r1 =
                     FStar_Ident.mk_ident (snd, (t.FStar_Syntax_Syntax.pos))
                      in
                   mk (FStar_Parser_AST.Projector (l, r1))
               | uu____2034 -> failwith "wrong projector format")
            else
              (let uu____2041 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2041
               then
                 let uu____2044 =
                   let uu____2045 =
                     let uu____2046 =
                       let uu____2052 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2052)  in
                     FStar_Ident.mk_ident uu____2046  in
                   FStar_Parser_AST.Tvar uu____2045  in
                 mk uu____2044
               else
                 (let uu____2057 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2057
                  then
                    let uu____2060 =
                      let uu____2061 =
                        let uu____2062 =
                          let uu____2068 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2068)  in
                        FStar_Ident.mk_ident uu____2062  in
                      FStar_Parser_AST.Tvar uu____2061  in
                    mk uu____2060
                  else
                    (let uu____2073 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2077 =
                            let uu____2079 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2079  in
                          let uu____2082 = FStar_String.get s Prims.int_zero
                             in
                          uu____2077 <> uu____2082)
                        in
                     if uu____2073
                     then
                       let uu____2087 =
                         let uu____2088 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2088  in
                       mk uu____2087
                     else
                       (let uu____2091 =
                          let uu____2092 =
                            let uu____2103 = maybe_shorten_fv env fv  in
                            (uu____2103, [])  in
                          FStar_Parser_AST.Construct uu____2092  in
                        mk uu____2091))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2121 = FStar_Options.print_universes ()  in
          if uu____2121
          then
            let univs =
              FStar_List.map
                (fun x  -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes
               in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd,args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____2152 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs
                      in
                   FStar_List.append args uu____2152  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd, args1)) r l
             | uu____2175 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2183 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2183
          then
            let uu____2186 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk uu____2186
          else mk (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2191 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2212 -> ("Type", true)  in
          (match uu____2191 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2224 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk uu____2224  in
               let uu____2225 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2225
               then
                 let uu____2228 =
                   let uu____2229 =
                     let uu____2236 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2236, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2229  in
                 mk uu____2228
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2241) ->
          let uu____2266 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2266 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2282 = FStar_Options.print_implicits ()  in
                 if uu____2282 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2320  ->
                         match uu____2320 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2360 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2360 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2370 = FStar_Options.print_implicits ()  in
                 if uu____2370 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2381 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2381 FStar_List.rev  in
               let rec aux body3 uu___2_2406 =
                 match uu___2_2406 with
                 | [] -> body3
                 | hd::tl ->
                     let body4 = mk (FStar_Parser_AST.Product ([hd], body3))
                        in
                     aux body4 tl
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2422 =
            let uu____2427 =
              let uu____2428 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2428]  in
            FStar_Syntax_Subst.open_term uu____2427 phi  in
          (match uu____2422 with
           | (x1,phi1) ->
               let b =
                 let uu____2450 =
                   let uu____2453 = FStar_List.hd x1  in
                   resugar_binder' env uu____2453 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2450  in
               let uu____2460 =
                 let uu____2461 =
                   let uu____2466 = resugar_term' env phi1  in
                   (b, uu____2466)  in
                 FStar_Parser_AST.Refine uu____2461  in
               mk uu____2460)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2468;
             FStar_Syntax_Syntax.vars = uu____2469;_},(e,uu____2471)::[])
          when
          (let uu____2512 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2512) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last uu___3_2561 =
            match uu___3_2561 with
            | hd::[] -> [hd]
            | hd::tl -> last tl
            | uu____2631 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2717,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2718))::tl ->
                  drop_implicits tl
              | uu____2737 -> args2  in
            let uu____2746 = drop_implicits args1  in
            match uu____2746 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2778::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2808 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2908  ->
                   match uu____2908 with
                   | (e2,qual) ->
                       let uu____2925 = resugar_term' env e2  in
                       let uu____2926 = resugar_imp env qual  in
                       (uu____2925, uu____2926)) args1
               in
            let uu____2927 = resugar_term' env e1  in
            match uu____2927 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd,previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc  ->
                     fun uu____2964  ->
                       match uu____2964 with
                       | (x,qual) -> mk (FStar_Parser_AST.App (acc, x, qual)))
                  e2 args2
             in
          let args1 =
            let uu____2980 = FStar_Options.print_implicits ()  in
            if uu____2980 then args else filter_imp args  in
          let uu____2995 = resugar_term_as_op e  in
          (match uu____2995 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____3008) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____3033  ->
                        match uu____3033 with
                        | (x,uu____3045) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix ->
                                 let uu____3054 =
                                   let uu____3055 =
                                     let uu____3056 =
                                       let uu____3063 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3063, [prefix; x1])  in
                                     FStar_Parser_AST.Op uu____3056  in
                                   mk uu____3055  in
                                 FStar_Pervasives_Native.Some uu____3054))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3067) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last args1  in
               let body =
                 match args2 with
                 | (b,uu____3093)::[] -> b
                 | uu____3110 -> failwith "wrong arguments to dtuple"  in
               let uu____3120 =
                 let uu____3121 = FStar_Syntax_Subst.compress body  in
                 uu____3121.FStar_Syntax_Syntax.n  in
               (match uu____3120 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3126) ->
                    let uu____3151 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3151 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3161 = FStar_Options.print_implicits ()
                              in
                           if uu____3161 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3178 =
                           let uu____3179 =
                             let uu____3190 =
                               FStar_List.map
                                 (fun uu____3201  ->
                                    FStar_Util.Inl uu____3201) xs3
                                in
                             (uu____3190, body3)  in
                           FStar_Parser_AST.Sum uu____3179  in
                         mk uu____3178)
                | uu____3208 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3231  ->
                              match uu____3231 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3249) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3258) when
               let uu____3266 =
                 FStar_Ident.string_of_lid FStar_Parser_Const.sread_lid  in
               ref_read = uu____3266 ->
               let uu____3269 = FStar_List.hd args1  in
               (match uu____3269 with
                | (t1,uu____3283) ->
                    let uu____3288 =
                      let uu____3289 = FStar_Syntax_Subst.compress t1  in
                      uu____3289.FStar_Syntax_Syntax.n  in
                    (match uu____3288 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         let uu____3293 =
                           FStar_Ident.string_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Util.field_projector_contains_constructor
                           uu____3293
                         ->
                         let f =
                           let uu____3296 =
                             let uu____3297 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             [uu____3297]  in
                           FStar_Ident.lid_of_path uu____3296
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3301 =
                           let uu____3302 =
                             let uu____3307 = resugar_term' env t1  in
                             (uu____3307, f)  in
                           FStar_Parser_AST.Project uu____3302  in
                         mk uu____3301
                     | uu____3308 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3309) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___426_3336  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3346 =
                           match new_args with
                           | (a1,uu____3356)::(a2,uu____3358)::[] -> (a1, a2)
                           | uu____3385 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3346 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3407 =
                                  let uu____3408 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3408.FStar_Syntax_Syntax.n  in
                                match uu____3407 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3413) ->
                                    let uu____3438 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3438 with | (x1,e2) -> e2)
                                | uu____3445 ->
                                    let uu____3446 =
                                      let uu____3448 =
                                        let uu____3450 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3450
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3448
                                       in
                                    failwith uu____3446
                                 in
                              let body1 =
                                let uu____3453 = decomp body  in
                                resugar_term' env uu____3453  in
                              let handler1 =
                                let uu____3455 = decomp handler  in
                                resugar_term' env uu____3455  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3463,uu____3464,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3496,uu____3497,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3534 =
                                      let uu____3535 =
                                        let uu____3544 = resugar_body t11  in
                                        (uu____3544, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3535
                                       in
                                    mk uu____3534
                                | uu____3547 ->
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
                                | uu____3605 -> []  in
                              let branches = resugar_branches handler1  in
                              mk (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3638 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3639) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3648) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3671) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3736,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3768,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3799 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3812 =
                   let uu____3813 = FStar_Syntax_Subst.compress body  in
                   uu____3813.FStar_Syntax_Syntax.n  in
                 match uu____3812 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3818) ->
                     let uu____3843 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3843 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3853 = FStar_Options.print_implicits ()
                               in
                            if uu____3853 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3869 =
                            let uu____3878 =
                              let uu____3879 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3879.FStar_Syntax_Syntax.n  in
                            match uu____3878 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3897 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3914,pats) ->
                                      let uu____3948 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3992  ->
                                                     match uu____3992 with
                                                     | (e2,uu____4000) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3948, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____4016 =
                                        mk
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____4016)
                                  | uu____4025 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3897 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4057 ->
                                let uu____4058 = resugar_term' env body2  in
                                ([], uu____4058)
                             in
                          (match uu____3869 with
                           | (pats,body3) ->
                               let uu____4075 = uncurry xs3 pats body3  in
                               (match uu____4075 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4106 =
                                        let uu____4107 =
                                          let uu____4126 =
                                            let uu____4137 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4137, pats1)  in
                                          (xs4, uu____4126, body4)  in
                                        FStar_Parser_AST.QForall uu____4107
                                         in
                                      mk uu____4106
                                    else
                                      (let uu____4160 =
                                         let uu____4161 =
                                           let uu____4180 =
                                             let uu____4191 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4191, pats1)  in
                                           (xs4, uu____4180, body4)  in
                                         FStar_Parser_AST.QExists uu____4161
                                          in
                                       mk uu____4160))))
                 | uu____4212 ->
                     if op = "forall"
                     then
                       let uu____4216 =
                         let uu____4217 =
                           let uu____4236 = resugar_term' env body  in
                           ([], ([], []), uu____4236)  in
                         FStar_Parser_AST.QForall uu____4217  in
                       mk uu____4216
                     else
                       (let uu____4259 =
                          let uu____4260 =
                            let uu____4279 = resugar_term' env body  in
                            ([], ([], []), uu____4279)  in
                          FStar_Parser_AST.QExists uu____4260  in
                        mk uu____4259)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last args1  in
                 (match args2 with
                  | (b,uu____4318)::[] -> resugar_forall_body b
                  | uu____4335 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4347) ->
               let uu____4355 = FStar_List.hd args1  in
               (match uu____4355 with
                | (e1,uu____4369) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity1) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4441  ->
                         match uu____4441 with
                         | (e1,qual) ->
                             let uu____4458 = resugar_term' env e1  in
                             let uu____4459 = resugar_imp env qual  in
                             (uu____4458, uu____4459)))
                  in
               (match expected_arity1 with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4475 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4475 with
                       | (op_args,rest) ->
                           let head =
                             let uu____4523 =
                               let uu____4524 =
                                 let uu____4531 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4531)  in
                               FStar_Parser_AST.Op uu____4524  in
                             mk uu____4523  in
                           FStar_List.fold_left
                             (fun head1  ->
                                fun uu____4549  ->
                                  match uu____4549 with
                                  | (arg,qual) ->
                                      mk
                                        (FStar_Parser_AST.App
                                           (head1, arg, qual))) head rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n when
                    (FStar_List.length args1) = n ->
                    let uu____4568 =
                      let uu____4569 =
                        let uu____4576 =
                          let uu____4579 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4579
                           in
                        (op1, uu____4576)  in
                      FStar_Parser_AST.Op uu____4569  in
                    mk uu____4568
                | uu____4592 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4661 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4661 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4707 =
                   let uu____4720 =
                     let uu____4725 = resugar_pat' env pat1 branch_bv  in
                     let uu____4726 = resugar_term' env e  in
                     (uu____4725, uu____4726)  in
                   (FStar_Pervasives_Native.None, uu____4720)  in
                 [uu____4707]  in
               let body = resugar_term' env t2  in
               mk
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4778,t1)::(pat2,uu____4781,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4877 =
            let uu____4878 =
              let uu____4885 = resugar_term' env e  in
              let uu____4886 = resugar_term' env t1  in
              let uu____4887 = resugar_term' env t2  in
              (uu____4885, uu____4886, uu____4887)  in
            FStar_Parser_AST.If uu____4878  in
          mk uu____4877
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4953 =
            match uu____4953 with
            | (pat,wopt,b) ->
                let uu____4995 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4995 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5047 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5047
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5051 =
            let uu____5052 =
              let uu____5067 = resugar_term' env e  in
              let uu____5068 = FStar_List.map resugar_branch branches  in
              (uu____5067, uu____5068)  in
            FStar_Parser_AST.Match uu____5052  in
          mk uu____5051
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5114) ->
          let term =
            match asc with
            | FStar_Util.Inl n -> resugar_term' env n
            | FStar_Util.Inr n -> resugar_comp' env n  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5183 =
            let uu____5184 =
              let uu____5193 = resugar_term' env e  in
              (uu____5193, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5184  in
          mk uu____5183
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5222 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5222 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5276 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5276
                    in
                 let uu____5283 =
                   let uu____5288 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5288
                    in
                 match uu____5283 with
                 | (univs,td) ->
                     let uu____5308 =
                       let uu____5315 =
                         let uu____5316 = FStar_Syntax_Subst.compress td  in
                         uu____5316.FStar_Syntax_Syntax.n  in
                       match uu____5315 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5325,(t1,uu____5327)::(d,uu____5329)::[])
                           -> (t1, d)
                       | uu____5386 -> failwith "wrong let binding format"
                        in
                     (match uu____5308 with
                      | (typ,def) ->
                          let uu____5417 =
                            let uu____5433 =
                              let uu____5434 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5434.FStar_Syntax_Syntax.n  in
                            match uu____5433 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5454) ->
                                let uu____5479 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5479 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5510 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5510
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5533 -> ([], def, false)  in
                          (match uu____5417 with
                           | (binders,term,is_pat_app) ->
                               let uu____5588 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5599 =
                                       let uu____5600 =
                                         let uu____5601 =
                                           let uu____5608 =
                                             bv_as_unique_ident bv  in
                                           (uu____5608,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5601
                                          in
                                       mk_pat uu____5600  in
                                     (uu____5599, term)
                                  in
                               (match uu____5588 with
                                | (pat,term1) ->
                                    let uu____5630 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5673  ->
                                                  match uu____5673 with
                                                  | (bv,q) ->
                                                      let uu____5688 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5688
                                                        (fun q1  ->
                                                           let uu____5700 =
                                                             let uu____5701 =
                                                               let uu____5708
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5708,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5701
                                                              in
                                                           mk_pat uu____5700)))
                                           in
                                        let uu____5711 =
                                          let uu____5716 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5716)
                                           in
                                        let uu____5719 =
                                          universe_to_string univs  in
                                        (uu____5711, uu____5719)
                                      else
                                        (let uu____5728 =
                                           let uu____5733 =
                                             resugar_term' env term1  in
                                           (pat, uu____5733)  in
                                         let uu____5734 =
                                           universe_to_string univs  in
                                         (uu____5728, uu____5734))
                                       in
                                    (attrs_opt, uu____5630))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5840 =
                   match uu____5840 with
                   | (attrs,(pb,univs)) ->
                       let uu____5900 =
                         let uu____5902 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5902  in
                       if uu____5900
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs (FStar_Pervasives_Native.snd pb))))
                    in
                 FStar_List.map f r  in
               let body2 = resugar_term' env body1  in
               mk
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5983) ->
          let s =
            let uu____6002 =
              let uu____6004 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____6004 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____6002  in
          let uu____6009 = mk FStar_Parser_AST.Wild  in label s uu____6009
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____6017 =
            let uu____6018 =
              let uu____6023 = resugar_term' env tm  in (uu____6023, qi1)  in
            FStar_Parser_AST.Quote uu____6018  in
          mk uu____6017
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_6035 =
            match uu___4_6035 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6043,(uu____6044,(p,t11))::[],t2) ->
                      mk (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6105 =
                        let uu____6106 =
                          let uu____6115 = resugar_seq t11  in
                          (uu____6115, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6106  in
                      mk uu____6105
                  | uu____6118 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6119,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6183  ->
                         match uu____6183 with
                         | (x,uu____6191) -> resugar_term' env x))
                  in
               mk (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6196 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6207,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6213,uu____6214,t1)
               -> resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun c  ->
      let mk a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____6254 = FStar_Options.print_universes ()  in
               if uu____6254
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.GTotal (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____6318 = FStar_Options.print_universes ()  in
               if uu____6318
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.Comp c1 ->
          let result =
            let uu____6362 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6362, FStar_Parser_AST.Nothing)  in
          let uu____6363 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6363
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6386 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6386
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6471 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6471, (FStar_Pervasives_Native.snd post))  in
                    let uu____6482 =
                      let uu____6491 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6491 then [] else [pre]  in
                    let uu____6526 =
                      let uu____6535 =
                        let uu____6544 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6544 then [] else [pats]  in
                      FStar_List.append [post1] uu____6535  in
                    FStar_List.append uu____6482 uu____6526
                | uu____6603 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6637  ->
                   match uu____6637 with
                   | (e,uu____6649) ->
                       let uu____6654 = resugar_term' env e  in
                       (uu____6654, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6679 =
              match uu___5_6679 with
              | [] -> l
              | hd::tl ->
                  (match hd with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6712 = resugar_term' env e  in
                         (uu____6712, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl
                   | uu____6717 -> aux l tl)
               in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
            mk
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk
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
        let uu____6764 = b  in
        match uu____6764 with
        | (x,aq) ->
            let uu____6773 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6773
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6787 =
                       let uu____6788 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6788  in
                     FStar_Parser_AST.mk_binder uu____6787 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6789 ->
                     let uu____6790 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6790
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6795 =
                          let uu____6796 =
                            let uu____6801 = bv_as_unique_ident x  in
                            (uu____6801, e)  in
                          FStar_Parser_AST.Annotated uu____6796  in
                        FStar_Parser_AST.mk_binder uu____6795 r
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
    fun v  ->
      fun aqual  ->
        fun body_bv  ->
          fun typ_opt  ->
            let mk a =
              let uu____6821 = FStar_Syntax_Syntax.range_of_bv v  in
              FStar_Parser_AST.mk_pattern a uu____6821  in
            let used = FStar_Util.set_mem v body_bv  in
            let pat =
              let uu____6825 =
                if used
                then
                  let uu____6827 =
                    let uu____6834 = bv_as_unique_ident v  in
                    (uu____6834, aqual)  in
                  FStar_Parser_AST.PatVar uu____6827
                else FStar_Parser_AST.PatWild aqual  in
              mk uu____6825  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6841;
                  FStar_Syntax_Syntax.vars = uu____6842;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6852 = FStar_Options.print_bound_var_types ()  in
                if uu____6852
                then
                  let uu____6855 =
                    let uu____6856 =
                      let uu____6867 =
                        let uu____6874 = resugar_term' env typ  in
                        (uu____6874, FStar_Pervasives_Native.None)  in
                      (pat, uu____6867)  in
                    FStar_Parser_AST.PatAscribed uu____6856  in
                  mk uu____6855
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
          let uu____6895 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6895
            (fun aqual  ->
               let uu____6907 =
                 let uu____6912 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun uu____6923  ->
                      FStar_Pervasives_Native.Some uu____6923) uu____6912
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6907)

and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun p  ->
      fun branch_bv  ->
        let mk a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b  ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None)
           in
        let may_drop_implicits args =
          (let uu____6985 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6985) &&
            (let uu____6988 =
               FStar_List.existsML
                 (fun uu____7001  ->
                    match uu____7001 with
                    | (pattern,is_implicit) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____7023)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____7028 -> false
                          | uu____7030 -> true  in
                        is_implicit && might_be_used) args
                in
             Prims.op_Negation uu____6988)
           in
        let resugar_plain_pat_cons' fv args =
          mk
            (FStar_Parser_AST.PatApp
               ((mk
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args))
           in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____7098 = may_drop_implicits args  in
            if uu____7098 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7123  ->
                 match uu____7123 with
                 | (p1,b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1
             in
          resugar_plain_pat_cons' fv args2
        
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
              mk
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____7178 =
                  let uu____7180 =
                    let uu____7182 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7182  in
                  Prims.op_Negation uu____7180  in
                if uu____7178
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____7226 = filter_pattern_imp args  in
              (match uu____7226 with
               | (hd,false )::(tl,false )::[] ->
                   let hd' = aux hd (FStar_Pervasives_Native.Some false)  in
                   let uu____7276 =
                     aux tl (FStar_Pervasives_Native.Some false)  in
                   (match uu____7276 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7295 =
                       let uu____7301 =
                         let uu____7303 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7303
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7301)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7295);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7356  ->
                        match uu____7356 with
                        | (p2,is_implicit) ->
                            if is_implicit
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7373 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7373)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7381;
                 FStar_Syntax_Syntax.fv_delta = uu____7382;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7411 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7411 FStar_List.rev  in
              let args1 =
                let uu____7427 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7447  ->
                          match uu____7447 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7427 FStar_List.rev  in
              let rec map2 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd::tl) -> []
                | (hd::tl,[]) ->
                    let uu____7525 = map2 tl []  in
                    (hd,
                      (mk
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7525
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7548 = map2 tl1 tl2  in (hd1, hd2) ::
                      uu____7548
                 in
              let args2 =
                let uu____7566 = map2 fields1 args1  in
                FStar_All.pipe_right uu____7566 FStar_List.rev  in
              mk (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v ->
              let uu____7610 =
                let uu____7621 =
                  FStar_Ident.text_of_id v.FStar_Syntax_Syntax.ppname  in
                string_to_op uu____7621  in
              (match uu____7610 with
               | FStar_Pervasives_Native.Some (op,uu____7624) ->
                   let uu____7641 =
                     let uu____7642 =
                       let uu____7643 =
                         let uu____7649 =
                           FStar_Ident.range_of_id
                             v.FStar_Syntax_Syntax.ppname
                            in
                         (op, uu____7649)  in
                       FStar_Ident.mk_ident uu____7643  in
                     FStar_Parser_AST.PatOp uu____7642  in
                   mk uu____7641
               | FStar_Pervasives_Native.None  ->
                   let uu____7659 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v uu____7659 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7664 ->
              let uu____7665 =
                let uu____7666 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7666  in
              mk uu____7665
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
          let uu____7706 =
            let uu____7709 =
              let uu____7710 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7710  in
            FStar_Pervasives_Native.Some uu____7709  in
          FStar_Pervasives_Native.Some uu____7706

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
          let uu____7722 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7722

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7730  ->
    match uu___6_7730 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7737 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7738 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7739 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7744 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7753 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7762 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7768  ->
    match uu___7_7768 with
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
            (tylid,uvs,bs,t,uu____7811,datacons) ->
            let uu____7821 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7849,uu____7850,uu____7851,inductive_lid,uu____7853,uu____7854)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7861 -> failwith "unexpected"))
               in
            (match uu____7821 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7882 = FStar_Options.print_implicits ()  in
                   if uu____7882 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7899 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7906  ->
                             match uu___8_7906 with
                             | FStar_Syntax_Syntax.RecordType uu____7908 ->
                                 true
                             | uu____7918 -> false))
                      in
                   if uu____7899
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7956,univs,term,uu____7959,num,uu____7961)
                           ->
                           let uu____7968 =
                             let uu____7969 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7969.FStar_Syntax_Syntax.n  in
                           (match uu____7968 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7979)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____8036  ->
                                          match uu____8036 with
                                          | (b,qual) ->
                                              let uu____8053 =
                                                bv_as_unique_ident b  in
                                              let uu____8054 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8053, uu____8054)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8059 -> failwith "unexpected")
                       | uu____8067 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     let uu____8092 =
                       let uu____8111 = FStar_Ident.ident_of_lid tylid  in
                       (uu____8111, bs2, FStar_Pervasives_Native.None,
                         fields)
                        in
                     FStar_Parser_AST.TyconRecord uu____8092
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs,term,uu____8182,num,uu____8184) ->
                            let c =
                              let uu____8201 = FStar_Ident.ident_of_lid l  in
                              let uu____8202 =
                                let uu____8205 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8205  in
                              (uu____8201, uu____8202, false)  in
                            c :: constructors
                        | uu____8219 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      let uu____8264 =
                        let uu____8288 = FStar_Ident.ident_of_lid tylid  in
                        (uu____8288, bs2, FStar_Pervasives_Native.None,
                          constructors)
                         in
                      FStar_Parser_AST.TyconVariant uu____8264)
                    in
                 (other_datacons, tyc))
        | uu____8304 ->
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
        let uu____8330 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8330;
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
        let uu____8360 = ts  in
        match uu____8360 with
        | (univs,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8373 =
              let uu____8374 =
                let uu____8385 =
                  let uu____8388 =
                    let uu____8389 =
                      let uu____8402 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____8402)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____8389  in
                  [uu____8388]  in
                (false, false, uu____8385)  in
              FStar_Parser_AST.Tycon uu____8374  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8373
  
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
              let uu____8467 = resugar_tscheme'' env name ts  in [uu____8467]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8485 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8487 =
             let uu____8490 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8492 =
               let uu____8495 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8497 =
                 let uu____8500 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8502 =
                   let uu____8505 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8507 =
                     let uu____8510 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8512 =
                       let uu____8515 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8515 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8510 :: uu____8512  in
                   uu____8505 :: uu____8507  in
                 uu____8500 :: uu____8502  in
               uu____8495 :: uu____8497  in
             uu____8490 :: uu____8492  in
           uu____8485 :: uu____8487)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8545 =
        match uu____8545 with
        | (ts,uu____8552) -> resugar_tscheme'' env name ts  in
      let uu____8553 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8555 =
        let uu____8558 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8560 =
          let uu____8563 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8565 =
            let uu____8568 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8570 =
              let uu____8573 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8573]  in
            uu____8568 :: uu____8570  in
          uu____8563 :: uu____8565  in
        uu____8558 :: uu____8560  in
      uu____8553 :: uu____8555
  
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
            let uu____8634 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8634 with
            | (bs,action_defn) ->
                let uu____8641 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8641 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8651 = FStar_Options.print_implicits ()  in
                       if uu____8651
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8661 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8661 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8678 =
                           let uu____8689 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8689,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8678  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
                       let uu____8710 =
                         let uu____8711 =
                           let uu____8722 =
                             let uu____8725 =
                               let uu____8726 =
                                 let uu____8739 =
                                   FStar_Ident.ident_of_lid
                                     d.FStar_Syntax_Syntax.action_name
                                    in
                                 (uu____8739, action_params2,
                                   FStar_Pervasives_Native.None, t)
                                  in
                               FStar_Parser_AST.TyconAbbrev uu____8726  in
                             [uu____8725]  in
                           (false, false, uu____8722)  in
                         FStar_Parser_AST.Tycon uu____8711  in
                       mk_decl r q uu____8710
                     else
                       (let uu____8752 =
                          let uu____8753 =
                            let uu____8764 =
                              let uu____8767 =
                                let uu____8768 =
                                  let uu____8781 =
                                    FStar_Ident.ident_of_lid
                                      d.FStar_Syntax_Syntax.action_name
                                     in
                                  (uu____8781, action_params2,
                                    FStar_Pervasives_Native.None,
                                    action_defn1)
                                   in
                                FStar_Parser_AST.TyconAbbrev uu____8768  in
                              [uu____8767]  in
                            (false, false, uu____8764)  in
                          FStar_Parser_AST.Tycon uu____8753  in
                        mk_decl r q uu____8752))
             in
          let eff_name =
            FStar_Ident.ident_of_lid ed.FStar_Syntax_Syntax.mname  in
          let uu____8793 =
            let uu____8798 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8798
             in
          match uu____8793 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8816 = FStar_Options.print_implicits ()  in
                if uu____8816 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8826 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8826 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8876) ->
          let uu____8885 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8908 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8926 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8934 -> false
                    | uu____8951 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8885 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8989 se1 =
                 match uu____8989 with
                 | (datacon_ses1,tycons) ->
                     let uu____9015 = resugar_typ env datacon_ses1 se1  in
                     (match uu____9015 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____9030 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____9030 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____9065 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____9065
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____9076,uu____9077,uu____9078,uu____9079,uu____9080)
                              ->
                              let uu____9087 =
                                let uu____9088 =
                                  let uu____9089 =
                                    let uu____9096 =
                                      FStar_Ident.ident_of_lid l  in
                                    (uu____9096,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Parser_AST.Exception uu____9089  in
                                decl'_to_decl se1 uu____9088  in
                              FStar_Pervasives_Native.Some uu____9087
                          | uu____9099 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____9103 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____9109 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9123) ->
          let uu____9128 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_9136  ->
                    match uu___9_9136 with
                    | FStar_Syntax_Syntax.Projector (uu____9138,uu____9139)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9141 -> true
                    | uu____9143 -> false))
             in
          if uu____9128
          then FStar_Pervasives_Native.None
          else
            (let mk e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng
                in
             let dummy = mk FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let = mk (FStar_Syntax_Syntax.Tm_let (lbs, dummy))
                in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____9178) ->
                 let uu____9207 =
                   let uu____9208 =
                     let uu____9209 =
                       let uu____9220 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9220)  in
                     FStar_Parser_AST.TopLevelLet uu____9209  in
                   decl'_to_decl se uu____9208  in
                 FStar_Pervasives_Native.Some uu____9207
             | uu____9257 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9262,fml) ->
          let uu____9264 =
            let uu____9265 =
              let uu____9266 =
                let uu____9271 = FStar_Ident.ident_of_lid lid  in
                let uu____9272 = resugar_term' env fml  in
                (uu____9271, uu____9272)  in
              FStar_Parser_AST.Assume uu____9266  in
            decl'_to_decl se uu____9265  in
          FStar_Pervasives_Native.Some uu____9264
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9274 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9274
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9283,t) ->
                let uu____9293 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9293
            | uu____9294 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9302,t) ->
                let uu____9312 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9312
            | uu____9313 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9337 -> failwith "Should not happen hopefully"  in
          let uu____9347 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9347
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9357 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9357 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9369 = FStar_Options.print_implicits ()  in
                 if uu____9369 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9385 =
                 let uu____9386 =
                   let uu____9387 =
                     let uu____9398 =
                       let uu____9401 =
                         let uu____9402 =
                           let uu____9415 = FStar_Ident.ident_of_lid lid  in
                           let uu____9416 = resugar_comp' env c1  in
                           (uu____9415, bs3, FStar_Pervasives_Native.None,
                             uu____9416)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____9402  in
                       [uu____9401]  in
                     (false, false, uu____9398)  in
                   FStar_Parser_AST.Tycon uu____9387  in
                 decl'_to_decl se uu____9386  in
               FStar_Pervasives_Native.Some uu____9385)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9428 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9428
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9432 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9440  ->
                    match uu___10_9440 with
                    | FStar_Syntax_Syntax.Projector (uu____9442,uu____9443)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9445 -> true
                    | uu____9447 -> false))
             in
          if uu____9432
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9455 =
                 (let uu____9459 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9459) || (FStar_List.isEmpty uvs)
                  in
               if uu____9455
               then resugar_term' env t
               else
                 (let uu____9464 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9464 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9473 = resugar_term' env t1  in
                      label universes uu____9473)
                in
             let uu____9474 =
               let uu____9475 =
                 let uu____9476 =
                   let uu____9481 = FStar_Ident.ident_of_lid lid  in
                   (uu____9481, t')  in
                 FStar_Parser_AST.Val uu____9476  in
               decl'_to_decl se uu____9475  in
             FStar_Pervasives_Native.Some uu____9474)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9488 =
            let uu____9489 =
              let uu____9490 =
                let uu____9497 =
                  FStar_List.map (fun l  -> FStar_Ident.ident_of_lid l) ids
                   in
                let uu____9502 = resugar_term' env t  in
                (uu____9497, uu____9502)  in
              FStar_Parser_AST.Splice uu____9490  in
            decl'_to_decl se uu____9489  in
          FStar_Pervasives_Native.Some uu____9488
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9505 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9522 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9538 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n,p,(uu____9542,t),uu____9544) ->
          let uu____9553 =
            let uu____9554 =
              let uu____9555 =
                let uu____9564 = resugar_term' env t  in
                (m, n, p, uu____9564)  in
              FStar_Parser_AST.Polymonadic_bind uu____9555  in
            decl'_to_decl se uu____9554  in
          FStar_Pervasives_Native.Some uu____9553
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9588 = noenv resugar_term'  in uu____9588 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9606 = noenv resugar_sigelt'  in uu____9606 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9624 = noenv resugar_comp'  in uu____9624 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9647 = noenv resugar_pat'  in uu____9647 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9681 = noenv resugar_binder'  in uu____9681 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9706 = noenv resugar_tscheme'  in uu____9706 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9734 = noenv resugar_eff_decl'  in uu____9734 r q ed
  