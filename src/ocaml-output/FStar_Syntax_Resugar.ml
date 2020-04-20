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
            let uu____464 =
              let uu____470 =
                let uu____472 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____472  in
              (uu____470, r)  in
            FStar_Ident.mk_ident uu____464  in
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
    let name_of_op uu___1_526 =
      match uu___1_526 with
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
      | uu____854 -> FStar_Pervasives_Native.None  in
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
    | uu____994 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____1012 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____1012 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1030 ->
               let maybeop =
                 let uu____1038 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1104)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1038
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
      let uu____1436 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1436 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1506 ->
          let length =
            let uu____1515 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____1515  in
          let str =
            if length = Prims.int_zero
            then
              FStar_Ident.string_of_lid
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            else
              (let uu____1525 =
                 FStar_Ident.string_of_lid
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_Util.substring_from uu____1525 (length + Prims.int_one))
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
                (let uu____1612 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1612
                 then
                   let uu____1625 =
                     let uu____1634 =
                       FStar_Ident.string_of_lid
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     (uu____1634, FStar_Pervasives_Native.None)  in
                   FStar_Pervasives_Native.Some uu____1625
                 else FStar_Pervasives_Native.None)
       in
    let uu____1659 =
      let uu____1660 = FStar_Syntax_Subst.compress t  in
      uu____1660.FStar_Syntax_Syntax.n  in
    match uu____1659 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length =
          let uu____1672 =
            FStar_Ident.nsstr
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_String.length uu____1672  in
        let s =
          if length = Prims.int_zero
          then
            FStar_Ident.string_of_lid
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          else
            (let uu____1682 =
               FStar_Ident.string_of_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.substring_from uu____1682 (length + Prims.int_one))
           in
        let uu____1685 = string_to_op s  in
        (match uu____1685 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1725 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1742 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1759 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1770 -> true
    | uu____1772 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let uu____1788 = FStar_Ident.string_of_lid lid  in
    match uu____1788 with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1795 ->
        let uu____1797 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1797
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1811 = may_shorten lid  in
      if uu____1811 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1956 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1956  in
      let uu____1959 =
        let uu____1960 = FStar_Syntax_Subst.compress t  in
        uu____1960.FStar_Syntax_Syntax.n  in
      match uu____1959 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1963 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1980 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1980
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1983 =
              let uu____1984 = bv_as_unique_ident x  in [uu____1984]  in
            FStar_Ident.lid_of_ids uu____1983  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1987 =
              let uu____1988 = bv_as_unique_ident x  in [uu____1988]  in
            FStar_Ident.lid_of_ids uu____1987  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length =
            let uu____1992 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____1992  in
          let s =
            if length = Prims.int_zero
            then FStar_Ident.string_of_lid a
            else
              (let uu____2002 = FStar_Ident.string_of_lid a  in
               FStar_Util.substring_from uu____2002 (length + Prims.int_one))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____2011 =
              let uu____2012 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____2012  in
            mk uu____2011
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
               | uu____2036 -> failwith "wrong projector format")
            else
              (let uu____2043 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2043
               then
                 let uu____2046 =
                   let uu____2047 =
                     let uu____2048 =
                       let uu____2054 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2054)  in
                     FStar_Ident.mk_ident uu____2048  in
                   FStar_Parser_AST.Tvar uu____2047  in
                 mk uu____2046
               else
                 (let uu____2059 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2059
                  then
                    let uu____2062 =
                      let uu____2063 =
                        let uu____2064 =
                          let uu____2070 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2070)  in
                        FStar_Ident.mk_ident uu____2064  in
                      FStar_Parser_AST.Tvar uu____2063  in
                    mk uu____2062
                  else
                    (let uu____2075 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2079 =
                            let uu____2081 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2081  in
                          let uu____2084 = FStar_String.get s Prims.int_zero
                             in
                          uu____2079 <> uu____2084)
                        in
                     if uu____2075
                     then
                       let uu____2089 =
                         let uu____2090 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2090  in
                       mk uu____2089
                     else
                       (let uu____2093 =
                          let uu____2094 =
                            let uu____2105 = maybe_shorten_fv env fv  in
                            (uu____2105, [])  in
                          FStar_Parser_AST.Construct uu____2094  in
                        mk uu____2093))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2123 = FStar_Options.print_universes ()  in
          if uu____2123
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
                   let uu____2154 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs
                      in
                   FStar_List.append args uu____2154  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd, args1)) r l
             | uu____2177 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2185 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2185
          then
            let uu____2188 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk uu____2188
          else mk (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2193 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2214 -> ("Type", true)  in
          (match uu____2193 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2226 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk uu____2226  in
               let uu____2227 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2227
               then
                 let uu____2230 =
                   let uu____2231 =
                     let uu____2238 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2238, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2231  in
                 mk uu____2230
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2243) ->
          let uu____2268 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2268 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2284 = FStar_Options.print_implicits ()  in
                 if uu____2284 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2322  ->
                         match uu____2322 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2362 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2362 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2372 = FStar_Options.print_implicits ()  in
                 if uu____2372 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2383 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2383 FStar_List.rev  in
               let rec aux body3 uu___2_2408 =
                 match uu___2_2408 with
                 | [] -> body3
                 | hd::tl ->
                     let body4 = mk (FStar_Parser_AST.Product ([hd], body3))
                        in
                     aux body4 tl
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2424 =
            let uu____2429 =
              let uu____2430 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2430]  in
            FStar_Syntax_Subst.open_term uu____2429 phi  in
          (match uu____2424 with
           | (x1,phi1) ->
               let b =
                 let uu____2452 =
                   let uu____2455 = FStar_List.hd x1  in
                   resugar_binder' env uu____2455 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2452  in
               let uu____2462 =
                 let uu____2463 =
                   let uu____2468 = resugar_term' env phi1  in
                   (b, uu____2468)  in
                 FStar_Parser_AST.Refine uu____2463  in
               mk uu____2462)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2470;
             FStar_Syntax_Syntax.vars = uu____2471;_},(e,uu____2473)::[])
          when
          (let uu____2514 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2514) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last uu___3_2563 =
            match uu___3_2563 with
            | hd::[] -> [hd]
            | hd::tl -> last tl
            | uu____2633 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2719,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2720))::tl ->
                  drop_implicits tl
              | uu____2739 -> args2  in
            let uu____2748 = drop_implicits args1  in
            match uu____2748 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2780::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2810 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2910  ->
                   match uu____2910 with
                   | (e2,qual) ->
                       let uu____2927 = resugar_term' env e2  in
                       let uu____2928 = resugar_imp env qual  in
                       (uu____2927, uu____2928)) args1
               in
            let uu____2929 = resugar_term' env e1  in
            match uu____2929 with
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
                     fun uu____2966  ->
                       match uu____2966 with
                       | (x,qual) -> mk (FStar_Parser_AST.App (acc, x, qual)))
                  e2 args2
             in
          let args1 =
            let uu____2982 = FStar_Options.print_implicits ()  in
            if uu____2982 then args else filter_imp args  in
          let uu____2997 = resugar_term_as_op e  in
          (match uu____2997 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____3010) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____3035  ->
                        match uu____3035 with
                        | (x,uu____3047) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix ->
                                 let uu____3056 =
                                   let uu____3057 =
                                     let uu____3058 =
                                       let uu____3065 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3065, [prefix; x1])  in
                                     FStar_Parser_AST.Op uu____3058  in
                                   mk uu____3057  in
                                 FStar_Pervasives_Native.Some uu____3056))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3069) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last args1  in
               let body =
                 match args2 with
                 | (b,uu____3095)::[] -> b
                 | uu____3112 -> failwith "wrong arguments to dtuple"  in
               let uu____3122 =
                 let uu____3123 = FStar_Syntax_Subst.compress body  in
                 uu____3123.FStar_Syntax_Syntax.n  in
               (match uu____3122 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3128) ->
                    let uu____3153 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3153 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3163 = FStar_Options.print_implicits ()
                              in
                           if uu____3163 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3180 =
                           let uu____3181 =
                             let uu____3192 =
                               FStar_List.map
                                 (fun uu____3203  ->
                                    FStar_Util.Inl uu____3203) xs3
                                in
                             (uu____3192, body3)  in
                           FStar_Parser_AST.Sum uu____3181  in
                         mk uu____3180)
                | uu____3210 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3233  ->
                              match uu____3233 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3251) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3260) when
               let uu____3268 =
                 FStar_Ident.string_of_lid FStar_Parser_Const.sread_lid  in
               ref_read = uu____3268 ->
               let uu____3271 = FStar_List.hd args1  in
               (match uu____3271 with
                | (t1,uu____3285) ->
                    let uu____3290 =
                      let uu____3291 = FStar_Syntax_Subst.compress t1  in
                      uu____3291.FStar_Syntax_Syntax.n  in
                    (match uu____3290 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         let uu____3295 =
                           FStar_Ident.string_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Util.field_projector_contains_constructor
                           uu____3295
                         ->
                         let f =
                           let uu____3298 =
                             let uu____3299 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             [uu____3299]  in
                           FStar_Ident.lid_of_path uu____3298
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3303 =
                           let uu____3304 =
                             let uu____3309 = resugar_term' env t1  in
                             (uu____3309, f)  in
                           FStar_Parser_AST.Project uu____3304  in
                         mk uu____3303
                     | uu____3310 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3311) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___426_3338  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3348 =
                           match new_args with
                           | (a1,uu____3358)::(a2,uu____3360)::[] -> (a1, a2)
                           | uu____3387 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3348 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3409 =
                                  let uu____3410 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3410.FStar_Syntax_Syntax.n  in
                                match uu____3409 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3415) ->
                                    let uu____3440 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3440 with | (x1,e2) -> e2)
                                | uu____3447 ->
                                    let uu____3448 =
                                      let uu____3450 =
                                        let uu____3452 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3452
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3450
                                       in
                                    failwith uu____3448
                                 in
                              let body1 =
                                let uu____3455 = decomp body  in
                                resugar_term' env uu____3455  in
                              let handler1 =
                                let uu____3457 = decomp handler  in
                                resugar_term' env uu____3457  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3465,uu____3466,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3498,uu____3499,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3536 =
                                      let uu____3537 =
                                        let uu____3546 = resugar_body t11  in
                                        (uu____3546, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3537
                                       in
                                    mk uu____3536
                                | uu____3549 ->
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
                                | uu____3607 -> []  in
                              let branches = resugar_branches handler1  in
                              mk (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3640 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3641) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3650) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3673) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3738,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3770,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3801 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3814 =
                   let uu____3815 = FStar_Syntax_Subst.compress body  in
                   uu____3815.FStar_Syntax_Syntax.n  in
                 match uu____3814 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3820) ->
                     let uu____3845 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3845 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3855 = FStar_Options.print_implicits ()
                               in
                            if uu____3855 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3871 =
                            let uu____3880 =
                              let uu____3881 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3881.FStar_Syntax_Syntax.n  in
                            match uu____3880 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3899 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3916,pats) ->
                                      let uu____3950 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3994  ->
                                                     match uu____3994 with
                                                     | (e2,uu____4002) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3950, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____4018 =
                                        mk
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____4018)
                                  | uu____4027 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3899 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4059 ->
                                let uu____4060 = resugar_term' env body2  in
                                ([], uu____4060)
                             in
                          (match uu____3871 with
                           | (pats,body3) ->
                               let uu____4077 = uncurry xs3 pats body3  in
                               (match uu____4077 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4108 =
                                        let uu____4109 =
                                          let uu____4128 =
                                            let uu____4139 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4139, pats1)  in
                                          (xs4, uu____4128, body4)  in
                                        FStar_Parser_AST.QForall uu____4109
                                         in
                                      mk uu____4108
                                    else
                                      (let uu____4162 =
                                         let uu____4163 =
                                           let uu____4182 =
                                             let uu____4193 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4193, pats1)  in
                                           (xs4, uu____4182, body4)  in
                                         FStar_Parser_AST.QExists uu____4163
                                          in
                                       mk uu____4162))))
                 | uu____4214 ->
                     if op = "forall"
                     then
                       let uu____4218 =
                         let uu____4219 =
                           let uu____4238 = resugar_term' env body  in
                           ([], ([], []), uu____4238)  in
                         FStar_Parser_AST.QForall uu____4219  in
                       mk uu____4218
                     else
                       (let uu____4261 =
                          let uu____4262 =
                            let uu____4281 = resugar_term' env body  in
                            ([], ([], []), uu____4281)  in
                          FStar_Parser_AST.QExists uu____4262  in
                        mk uu____4261)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last args1  in
                 (match args2 with
                  | (b,uu____4320)::[] -> resugar_forall_body b
                  | uu____4337 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4349) ->
               let uu____4357 = FStar_List.hd args1  in
               (match uu____4357 with
                | (e1,uu____4371) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity1) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4443  ->
                         match uu____4443 with
                         | (e1,qual) ->
                             let uu____4460 = resugar_term' env e1  in
                             let uu____4461 = resugar_imp env qual  in
                             (uu____4460, uu____4461)))
                  in
               (match expected_arity1 with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4477 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4477 with
                       | (op_args,rest) ->
                           let head =
                             let uu____4525 =
                               let uu____4526 =
                                 let uu____4533 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4533)  in
                               FStar_Parser_AST.Op uu____4526  in
                             mk uu____4525  in
                           FStar_List.fold_left
                             (fun head1  ->
                                fun uu____4551  ->
                                  match uu____4551 with
                                  | (arg,qual) ->
                                      mk
                                        (FStar_Parser_AST.App
                                           (head1, arg, qual))) head rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n when
                    (FStar_List.length args1) = n ->
                    let uu____4570 =
                      let uu____4571 =
                        let uu____4578 =
                          let uu____4581 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4581
                           in
                        (op1, uu____4578)  in
                      FStar_Parser_AST.Op uu____4571  in
                    mk uu____4570
                | uu____4594 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4663 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4663 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4709 =
                   let uu____4722 =
                     let uu____4727 = resugar_pat' env pat1 branch_bv  in
                     let uu____4728 = resugar_term' env e  in
                     (uu____4727, uu____4728)  in
                   (FStar_Pervasives_Native.None, uu____4722)  in
                 [uu____4709]  in
               let body = resugar_term' env t2  in
               mk
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4780,t1)::(pat2,uu____4783,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4879 =
            let uu____4880 =
              let uu____4887 = resugar_term' env e  in
              let uu____4888 = resugar_term' env t1  in
              let uu____4889 = resugar_term' env t2  in
              (uu____4887, uu____4888, uu____4889)  in
            FStar_Parser_AST.If uu____4880  in
          mk uu____4879
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4955 =
            match uu____4955 with
            | (pat,wopt,b) ->
                let uu____4997 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4997 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5049 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5049
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5053 =
            let uu____5054 =
              let uu____5069 = resugar_term' env e  in
              let uu____5070 = FStar_List.map resugar_branch branches  in
              (uu____5069, uu____5070)  in
            FStar_Parser_AST.Match uu____5054  in
          mk uu____5053
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5116) ->
          let term =
            match asc with
            | FStar_Util.Inl n -> resugar_term' env n
            | FStar_Util.Inr n -> resugar_comp' env n  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5185 =
            let uu____5186 =
              let uu____5195 = resugar_term' env e  in
              (uu____5195, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5186  in
          mk uu____5185
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5224 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5224 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5278 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5278
                    in
                 let uu____5285 =
                   let uu____5290 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5290
                    in
                 match uu____5285 with
                 | (univs,td) ->
                     let uu____5310 =
                       let uu____5317 =
                         let uu____5318 = FStar_Syntax_Subst.compress td  in
                         uu____5318.FStar_Syntax_Syntax.n  in
                       match uu____5317 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5327,(t1,uu____5329)::(d,uu____5331)::[])
                           -> (t1, d)
                       | uu____5388 -> failwith "wrong let binding format"
                        in
                     (match uu____5310 with
                      | (typ,def) ->
                          let uu____5419 =
                            let uu____5435 =
                              let uu____5436 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5436.FStar_Syntax_Syntax.n  in
                            match uu____5435 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5456) ->
                                let uu____5481 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5481 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5512 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5512
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5535 -> ([], def, false)  in
                          (match uu____5419 with
                           | (binders,term,is_pat_app) ->
                               let uu____5590 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5601 =
                                       let uu____5602 =
                                         let uu____5603 =
                                           let uu____5610 =
                                             bv_as_unique_ident bv  in
                                           (uu____5610,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5603
                                          in
                                       mk_pat uu____5602  in
                                     (uu____5601, term)
                                  in
                               (match uu____5590 with
                                | (pat,term1) ->
                                    let uu____5632 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5675  ->
                                                  match uu____5675 with
                                                  | (bv,q) ->
                                                      let uu____5690 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5690
                                                        (fun q1  ->
                                                           let uu____5702 =
                                                             let uu____5703 =
                                                               let uu____5710
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5710,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5703
                                                              in
                                                           mk_pat uu____5702)))
                                           in
                                        let uu____5713 =
                                          let uu____5718 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5718)
                                           in
                                        let uu____5721 =
                                          universe_to_string univs  in
                                        (uu____5713, uu____5721)
                                      else
                                        (let uu____5730 =
                                           let uu____5735 =
                                             resugar_term' env term1  in
                                           (pat, uu____5735)  in
                                         let uu____5736 =
                                           universe_to_string univs  in
                                         (uu____5730, uu____5736))
                                       in
                                    (attrs_opt, uu____5632))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5842 =
                   match uu____5842 with
                   | (attrs,(pb,univs)) ->
                       let uu____5902 =
                         let uu____5904 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5904  in
                       if uu____5902
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5985) ->
          let s =
            let uu____6004 =
              let uu____6006 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____6006 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____6004  in
          let uu____6011 = mk FStar_Parser_AST.Wild  in label s uu____6011
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____6019 =
            let uu____6020 =
              let uu____6025 = resugar_term' env tm  in (uu____6025, qi1)  in
            FStar_Parser_AST.Quote uu____6020  in
          mk uu____6019
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_6037 =
            match uu___4_6037 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6045,(uu____6046,(p,t11))::[],t2) ->
                      mk (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6107 =
                        let uu____6108 =
                          let uu____6117 = resugar_seq t11  in
                          (uu____6117, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6108  in
                      mk uu____6107
                  | uu____6120 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6121,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6185  ->
                         match uu____6185 with
                         | (x,uu____6193) -> resugar_term' env x))
                  in
               mk (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6198 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6209,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6215,uu____6216,t1)
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
               let uu____6256 = FStar_Options.print_universes ()  in
               if uu____6256
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
               let uu____6320 = FStar_Options.print_universes ()  in
               if uu____6320
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
            let uu____6364 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6364, FStar_Parser_AST.Nothing)  in
          let uu____6365 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6365
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6388 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6388
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6473 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6473, (FStar_Pervasives_Native.snd post))  in
                    let uu____6484 =
                      let uu____6493 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6493 then [] else [pre]  in
                    let uu____6528 =
                      let uu____6537 =
                        let uu____6546 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6546 then [] else [pats]  in
                      FStar_List.append [post1] uu____6537  in
                    FStar_List.append uu____6484 uu____6528
                | uu____6605 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6639  ->
                   match uu____6639 with
                   | (e,uu____6651) ->
                       let uu____6656 = resugar_term' env e  in
                       (uu____6656, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6681 =
              match uu___5_6681 with
              | [] -> l
              | hd::tl ->
                  (match hd with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6714 = resugar_term' env e  in
                         (uu____6714, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl
                   | uu____6719 -> aux l tl)
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
        let uu____6766 = b  in
        match uu____6766 with
        | (x,aq) ->
            let uu____6775 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6775
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6789 =
                       let uu____6790 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6790  in
                     FStar_Parser_AST.mk_binder uu____6789 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6791 ->
                     let uu____6792 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6792
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6797 =
                          let uu____6798 =
                            let uu____6803 = bv_as_unique_ident x  in
                            (uu____6803, e)  in
                          FStar_Parser_AST.Annotated uu____6798  in
                        FStar_Parser_AST.mk_binder uu____6797 r
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
              let uu____6823 = FStar_Syntax_Syntax.range_of_bv v  in
              FStar_Parser_AST.mk_pattern a uu____6823  in
            let used = FStar_Util.set_mem v body_bv  in
            let pat =
              let uu____6827 =
                if used
                then
                  let uu____6829 =
                    let uu____6836 = bv_as_unique_ident v  in
                    (uu____6836, aqual)  in
                  FStar_Parser_AST.PatVar uu____6829
                else FStar_Parser_AST.PatWild aqual  in
              mk uu____6827  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6843;
                  FStar_Syntax_Syntax.vars = uu____6844;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6854 = FStar_Options.print_bound_var_types ()  in
                if uu____6854
                then
                  let uu____6857 =
                    let uu____6858 =
                      let uu____6869 =
                        let uu____6876 = resugar_term' env typ  in
                        (uu____6876, FStar_Pervasives_Native.None)  in
                      (pat, uu____6869)  in
                    FStar_Parser_AST.PatAscribed uu____6858  in
                  mk uu____6857
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
          let uu____6897 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6897
            (fun aqual  ->
               let uu____6909 =
                 let uu____6914 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun uu____6925  ->
                      FStar_Pervasives_Native.Some uu____6925) uu____6914
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6909)

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
          (let uu____6987 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6987) &&
            (let uu____6990 =
               FStar_List.existsML
                 (fun uu____7003  ->
                    match uu____7003 with
                    | (pattern,is_implicit) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____7025)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____7030 -> false
                          | uu____7032 -> true  in
                        is_implicit && might_be_used) args
                in
             Prims.op_Negation uu____6990)
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
            let uu____7100 = may_drop_implicits args  in
            if uu____7100 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7125  ->
                 match uu____7125 with
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
              ((let uu____7180 =
                  let uu____7182 =
                    let uu____7184 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7184  in
                  Prims.op_Negation uu____7182  in
                if uu____7180
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
              let uu____7228 = filter_pattern_imp args  in
              (match uu____7228 with
               | (hd,false )::(tl,false )::[] ->
                   let hd' = aux hd (FStar_Pervasives_Native.Some false)  in
                   let uu____7278 =
                     aux tl (FStar_Pervasives_Native.Some false)  in
                   (match uu____7278 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7297 =
                       let uu____7303 =
                         let uu____7305 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7305
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7303)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7297);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7358  ->
                        match uu____7358 with
                        | (p2,is_implicit) ->
                            if is_implicit
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7375 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7375)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7383;
                 FStar_Syntax_Syntax.fv_delta = uu____7384;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7413 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7413 FStar_List.rev  in
              let args1 =
                let uu____7429 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7449  ->
                          match uu____7449 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7429 FStar_List.rev  in
              let rec map2 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd::tl) -> []
                | (hd::tl,[]) ->
                    let uu____7527 = map2 tl []  in
                    (hd,
                      (mk
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7527
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7550 = map2 tl1 tl2  in (hd1, hd2) ::
                      uu____7550
                 in
              let args2 =
                let uu____7568 = map2 fields1 args1  in
                FStar_All.pipe_right uu____7568 FStar_List.rev  in
              mk (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v ->
              let uu____7612 =
                let uu____7623 =
                  FStar_Ident.text_of_id v.FStar_Syntax_Syntax.ppname  in
                string_to_op uu____7623  in
              (match uu____7612 with
               | FStar_Pervasives_Native.Some (op,uu____7626) ->
                   let uu____7643 =
                     let uu____7644 =
                       let uu____7645 =
                         let uu____7651 =
                           FStar_Ident.range_of_id
                             v.FStar_Syntax_Syntax.ppname
                            in
                         (op, uu____7651)  in
                       FStar_Ident.mk_ident uu____7645  in
                     FStar_Parser_AST.PatOp uu____7644  in
                   mk uu____7643
               | FStar_Pervasives_Native.None  ->
                   let uu____7661 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v uu____7661 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7666 ->
              let uu____7667 =
                let uu____7668 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7668  in
              mk uu____7667
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
          let uu____7708 =
            let uu____7711 =
              let uu____7712 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7712  in
            FStar_Pervasives_Native.Some uu____7711  in
          FStar_Pervasives_Native.Some uu____7708

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
          let uu____7724 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7724

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7732  ->
    match uu___6_7732 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7739 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7740 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7741 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7746 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7755 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7764 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7770  ->
    match uu___7_7770 with
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
            (tylid,uvs,bs,t,uu____7813,datacons) ->
            let uu____7823 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7851,uu____7852,uu____7853,inductive_lid,uu____7855,uu____7856)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7863 -> failwith "unexpected"))
               in
            (match uu____7823 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7884 = FStar_Options.print_implicits ()  in
                   if uu____7884 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7901 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7908  ->
                             match uu___8_7908 with
                             | FStar_Syntax_Syntax.RecordType uu____7910 ->
                                 true
                             | uu____7920 -> false))
                      in
                   if uu____7901
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7958,univs,term,uu____7961,num,uu____7963)
                           ->
                           let uu____7970 =
                             let uu____7971 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7971.FStar_Syntax_Syntax.n  in
                           (match uu____7970 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7981)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____8038  ->
                                          match uu____8038 with
                                          | (b,qual) ->
                                              let uu____8055 =
                                                bv_as_unique_ident b  in
                                              let uu____8056 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8055, uu____8056)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8061 -> failwith "unexpected")
                       | uu____8069 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     let uu____8094 =
                       let uu____8113 = FStar_Ident.ident_of_lid tylid  in
                       (uu____8113, bs2, FStar_Pervasives_Native.None,
                         fields)
                        in
                     FStar_Parser_AST.TyconRecord uu____8094
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs,term,uu____8184,num,uu____8186) ->
                            let c =
                              let uu____8203 = FStar_Ident.ident_of_lid l  in
                              let uu____8204 =
                                let uu____8207 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8207  in
                              (uu____8203, uu____8204, false)  in
                            c :: constructors
                        | uu____8221 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      let uu____8266 =
                        let uu____8290 = FStar_Ident.ident_of_lid tylid  in
                        (uu____8290, bs2, FStar_Pervasives_Native.None,
                          constructors)
                         in
                      FStar_Parser_AST.TyconVariant uu____8266)
                    in
                 (other_datacons, tyc))
        | uu____8306 ->
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
        let uu____8332 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8332;
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
        let uu____8362 = ts  in
        match uu____8362 with
        | (univs,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8375 =
              let uu____8376 =
                let uu____8387 =
                  let uu____8390 =
                    let uu____8391 =
                      let uu____8404 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____8404)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____8391  in
                  [uu____8390]  in
                (false, false, uu____8387)  in
              FStar_Parser_AST.Tycon uu____8376  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8375
  
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
              let uu____8469 = resugar_tscheme'' env name ts  in [uu____8469]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8487 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8489 =
             let uu____8492 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8494 =
               let uu____8497 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8499 =
                 let uu____8502 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8504 =
                   let uu____8507 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8509 =
                     let uu____8512 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8514 =
                       let uu____8517 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8517 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8512 :: uu____8514  in
                   uu____8507 :: uu____8509  in
                 uu____8502 :: uu____8504  in
               uu____8497 :: uu____8499  in
             uu____8492 :: uu____8494  in
           uu____8487 :: uu____8489)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8547 =
        match uu____8547 with
        | (ts,uu____8554) -> resugar_tscheme'' env name ts  in
      let uu____8555 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8557 =
        let uu____8560 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8562 =
          let uu____8565 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8567 =
            let uu____8570 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8572 =
              let uu____8575 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8575]  in
            uu____8570 :: uu____8572  in
          uu____8565 :: uu____8567  in
        uu____8560 :: uu____8562  in
      uu____8555 :: uu____8557
  
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
            let uu____8636 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8636 with
            | (bs,action_defn) ->
                let uu____8643 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8643 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8653 = FStar_Options.print_implicits ()  in
                       if uu____8653
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8663 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8663 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8680 =
                           let uu____8691 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8691,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8680  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
                       let uu____8712 =
                         let uu____8713 =
                           let uu____8724 =
                             let uu____8727 =
                               let uu____8728 =
                                 let uu____8741 =
                                   FStar_Ident.ident_of_lid
                                     d.FStar_Syntax_Syntax.action_name
                                    in
                                 (uu____8741, action_params2,
                                   FStar_Pervasives_Native.None, t)
                                  in
                               FStar_Parser_AST.TyconAbbrev uu____8728  in
                             [uu____8727]  in
                           (false, false, uu____8724)  in
                         FStar_Parser_AST.Tycon uu____8713  in
                       mk_decl r q uu____8712
                     else
                       (let uu____8754 =
                          let uu____8755 =
                            let uu____8766 =
                              let uu____8769 =
                                let uu____8770 =
                                  let uu____8783 =
                                    FStar_Ident.ident_of_lid
                                      d.FStar_Syntax_Syntax.action_name
                                     in
                                  (uu____8783, action_params2,
                                    FStar_Pervasives_Native.None,
                                    action_defn1)
                                   in
                                FStar_Parser_AST.TyconAbbrev uu____8770  in
                              [uu____8769]  in
                            (false, false, uu____8766)  in
                          FStar_Parser_AST.Tycon uu____8755  in
                        mk_decl r q uu____8754))
             in
          let eff_name =
            FStar_Ident.ident_of_lid ed.FStar_Syntax_Syntax.mname  in
          let uu____8795 =
            let uu____8800 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8800
             in
          match uu____8795 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8818 = FStar_Options.print_implicits ()  in
                if uu____8818 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8828 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8828 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8878) ->
          let uu____8887 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8910 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8928 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8936 -> false
                    | uu____8953 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8887 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8991 se1 =
                 match uu____8991 with
                 | (datacon_ses1,tycons) ->
                     let uu____9017 = resugar_typ env datacon_ses1 se1  in
                     (match uu____9017 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____9032 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____9032 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____9067 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____9067
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____9078,uu____9079,uu____9080,uu____9081,uu____9082)
                              ->
                              let uu____9089 =
                                let uu____9090 =
                                  let uu____9091 =
                                    let uu____9098 =
                                      FStar_Ident.ident_of_lid l  in
                                    (uu____9098,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Parser_AST.Exception uu____9091  in
                                decl'_to_decl se1 uu____9090  in
                              FStar_Pervasives_Native.Some uu____9089
                          | uu____9101 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____9105 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____9111 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9125) ->
          let uu____9130 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_9138  ->
                    match uu___9_9138 with
                    | FStar_Syntax_Syntax.Projector (uu____9140,uu____9141)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9143 -> true
                    | uu____9145 -> false))
             in
          if uu____9130
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9180) ->
                 let uu____9209 =
                   let uu____9210 =
                     let uu____9211 =
                       let uu____9222 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9222)  in
                     FStar_Parser_AST.TopLevelLet uu____9211  in
                   decl'_to_decl se uu____9210  in
                 FStar_Pervasives_Native.Some uu____9209
             | uu____9259 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9264,fml) ->
          let uu____9266 =
            let uu____9267 =
              let uu____9268 =
                let uu____9273 = FStar_Ident.ident_of_lid lid  in
                let uu____9274 = resugar_term' env fml  in
                (uu____9273, uu____9274)  in
              FStar_Parser_AST.Assume uu____9268  in
            decl'_to_decl se uu____9267  in
          FStar_Pervasives_Native.Some uu____9266
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9276 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9276
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9285,t) ->
                let uu____9295 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9295
            | uu____9296 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9304,t) ->
                let uu____9314 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9314
            | uu____9315 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9339 -> failwith "Should not happen hopefully"  in
          let uu____9349 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9349
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9359 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9359 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9371 = FStar_Options.print_implicits ()  in
                 if uu____9371 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9387 =
                 let uu____9388 =
                   let uu____9389 =
                     let uu____9400 =
                       let uu____9403 =
                         let uu____9404 =
                           let uu____9417 = FStar_Ident.ident_of_lid lid  in
                           let uu____9418 = resugar_comp' env c1  in
                           (uu____9417, bs3, FStar_Pervasives_Native.None,
                             uu____9418)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____9404  in
                       [uu____9403]  in
                     (false, false, uu____9400)  in
                   FStar_Parser_AST.Tycon uu____9389  in
                 decl'_to_decl se uu____9388  in
               FStar_Pervasives_Native.Some uu____9387)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9430 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9430
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9434 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9442  ->
                    match uu___10_9442 with
                    | FStar_Syntax_Syntax.Projector (uu____9444,uu____9445)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9447 -> true
                    | uu____9449 -> false))
             in
          if uu____9434
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9457 =
                 (let uu____9461 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9461) || (FStar_List.isEmpty uvs)
                  in
               if uu____9457
               then resugar_term' env t
               else
                 (let uu____9466 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9466 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9475 = resugar_term' env t1  in
                      label universes uu____9475)
                in
             let uu____9476 =
               let uu____9477 =
                 let uu____9478 =
                   let uu____9483 = FStar_Ident.ident_of_lid lid  in
                   (uu____9483, t')  in
                 FStar_Parser_AST.Val uu____9478  in
               decl'_to_decl se uu____9477  in
             FStar_Pervasives_Native.Some uu____9476)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9490 =
            let uu____9491 =
              let uu____9492 =
                let uu____9499 =
                  FStar_List.map (fun l  -> FStar_Ident.ident_of_lid l) ids
                   in
                let uu____9504 = resugar_term' env t  in
                (uu____9499, uu____9504)  in
              FStar_Parser_AST.Splice uu____9492  in
            decl'_to_decl se uu____9491  in
          FStar_Pervasives_Native.Some uu____9490
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9507 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9524 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n,p,(uu____9543,t),uu____9545) ->
          let uu____9554 =
            let uu____9555 =
              let uu____9556 =
                let uu____9565 = resugar_term' env t  in
                (m, n, p, uu____9565)  in
              FStar_Parser_AST.Polymonadic_bind uu____9556  in
            decl'_to_decl se uu____9555  in
          FStar_Pervasives_Native.Some uu____9554
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9589 = noenv resugar_term'  in uu____9589 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9607 = noenv resugar_sigelt'  in uu____9607 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9625 = noenv resugar_comp'  in uu____9625 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9648 = noenv resugar_pat'  in uu____9648 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9682 = noenv resugar_binder'  in uu____9682 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9707 = noenv resugar_tscheme'  in uu____9707 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9735 = noenv resugar_eff_decl'  in uu____9735 r q ed
  