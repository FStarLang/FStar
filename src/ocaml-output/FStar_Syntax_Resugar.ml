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
  'uuuuuu74 .
    ('uuuuuu74 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu74 * FStar_Syntax_Syntax.arg_qualifier
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
  'uuuuuu170 .
    ('uuuuuu170 * Prims.bool) Prims.list ->
      ('uuuuuu170 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____205  ->
         match uu____205 with
         | (uu____212,is_implicit) -> Prims.op_Negation is_implicit) xs
  
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
      | uu____262 -> (n, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs  ->
    let uu____275 = FStar_Options.print_universes ()  in
    if uu____275
    then
      let uu____279 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs
         in
      FStar_All.pipe_right uu____279 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____328 ->
          let uu____329 = universe_to_int Prims.int_zero u  in
          (match uu____329 with
           | (n,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____340 =
                      let uu____341 =
                        let uu____342 =
                          let uu____354 = FStar_Util.string_of_int n  in
                          (uu____354, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____342  in
                      FStar_Parser_AST.Const uu____341  in
                    mk uu____340 r
                | uu____367 ->
                    let e1 =
                      let uu____369 =
                        let uu____370 =
                          let uu____371 =
                            let uu____383 = FStar_Util.string_of_int n  in
                            (uu____383, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____371  in
                        FStar_Parser_AST.Const uu____370  in
                      mk uu____369 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____397 =
                      let uu____398 =
                        let uu____405 = FStar_Ident.id_of_text "+"  in
                        (uu____405, [e1; e2])  in
                      FStar_Parser_AST.Op uu____398  in
                    mk uu____397 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____413 ->
               let t =
                 let uu____417 =
                   let uu____418 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____418  in
                 mk uu____417 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____427 =
                        let uu____428 =
                          let uu____435 = resugar_universe x r  in
                          (acc, uu____435, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____428  in
                      mk uu____427 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____437 -> mk FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____449 =
              let uu____455 =
                let uu____457 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____457  in
              (uu____455, r)  in
            FStar_Ident.mk_ident uu____449  in
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
          let length =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length = Prims.int_zero
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length + Prims.int_one)
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
        let length =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length = Prims.int_zero
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length + Prims.int_one)
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
      let mk a =
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
          let uu____1944 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1944
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1947 =
              let uu____1950 = bv_as_unique_ident x  in [uu____1950]  in
            FStar_Ident.lid_of_ids uu____1947  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1953 =
              let uu____1956 = bv_as_unique_ident x  in [uu____1956]  in
            FStar_Ident.lid_of_ids uu____1953  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length = Prims.int_zero
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length + Prims.int_one)
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____1975 =
              let uu____1976 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1976  in
            mk uu____1975
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
               | uu____2000 -> failwith "wrong projector format")
            else
              (let uu____2007 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2007
               then
                 let uu____2010 =
                   let uu____2011 =
                     let uu____2012 =
                       let uu____2018 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2018)  in
                     FStar_Ident.mk_ident uu____2012  in
                   FStar_Parser_AST.Tvar uu____2011  in
                 mk uu____2010
               else
                 (let uu____2023 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2023
                  then
                    let uu____2026 =
                      let uu____2027 =
                        let uu____2028 =
                          let uu____2034 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2034)  in
                        FStar_Ident.mk_ident uu____2028  in
                      FStar_Parser_AST.Tvar uu____2027  in
                    mk uu____2026
                  else
                    (let uu____2039 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2043 =
                            let uu____2045 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2045  in
                          let uu____2048 = FStar_String.get s Prims.int_zero
                             in
                          uu____2043 <> uu____2048)
                        in
                     if uu____2039
                     then
                       let uu____2053 =
                         let uu____2054 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2054  in
                       mk uu____2053
                     else
                       (let uu____2057 =
                          let uu____2058 =
                            let uu____2069 = maybe_shorten_fv env fv  in
                            (uu____2069, [])  in
                          FStar_Parser_AST.Construct uu____2058  in
                        mk uu____2057))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2087 = FStar_Options.print_universes ()  in
          if uu____2087
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
                   let uu____2118 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs
                      in
                   FStar_List.append args uu____2118  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd, args1)) r l
             | uu____2141 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2149 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2149
          then
            let uu____2152 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk uu____2152
          else mk (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2157 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2178 -> ("Type", true)  in
          (match uu____2157 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2190 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk uu____2190  in
               let uu____2191 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2191
               then
                 let uu____2194 =
                   let uu____2195 =
                     let uu____2202 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2202, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2195  in
                 mk uu____2194
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2207) ->
          let uu____2232 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2232 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2248 = FStar_Options.print_implicits ()  in
                 if uu____2248 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2286  ->
                         match uu____2286 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2326 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2326 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2336 = FStar_Options.print_implicits ()  in
                 if uu____2336 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2347 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2347 FStar_List.rev  in
               let rec aux body3 uu___2_2372 =
                 match uu___2_2372 with
                 | [] -> body3
                 | hd::tl ->
                     let body4 = mk (FStar_Parser_AST.Product ([hd], body3))
                        in
                     aux body4 tl
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2388 =
            let uu____2393 =
              let uu____2394 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2394]  in
            FStar_Syntax_Subst.open_term uu____2393 phi  in
          (match uu____2388 with
           | (x1,phi1) ->
               let b =
                 let uu____2416 =
                   let uu____2419 = FStar_List.hd x1  in
                   resugar_binder' env uu____2419 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2416  in
               let uu____2426 =
                 let uu____2427 =
                   let uu____2432 = resugar_term' env phi1  in
                   (b, uu____2432)  in
                 FStar_Parser_AST.Refine uu____2427  in
               mk uu____2426)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2434;
             FStar_Syntax_Syntax.vars = uu____2435;_},(e,uu____2437)::[])
          when
          (let uu____2478 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2478) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last uu___3_2527 =
            match uu___3_2527 with
            | hd::[] -> [hd]
            | hd::tl -> last tl
            | uu____2597 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2683,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2684))::tl ->
                  drop_implicits tl
              | uu____2703 -> args2  in
            let uu____2712 = drop_implicits args1  in
            match uu____2712 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2744::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2774 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2874  ->
                   match uu____2874 with
                   | (e2,qual) ->
                       let uu____2891 = resugar_term' env e2  in
                       let uu____2892 = resugar_imp env qual  in
                       (uu____2891, uu____2892)) args1
               in
            let uu____2893 = resugar_term' env e1  in
            match uu____2893 with
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
                     fun uu____2930  ->
                       match uu____2930 with
                       | (x,qual) -> mk (FStar_Parser_AST.App (acc, x, qual)))
                  e2 args2
             in
          let args1 =
            let uu____2946 = FStar_Options.print_implicits ()  in
            if uu____2946 then args else filter_imp args  in
          let uu____2961 = resugar_term_as_op e  in
          (match uu____2961 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2974) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2999  ->
                        match uu____2999 with
                        | (x,uu____3011) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix ->
                                 let uu____3020 =
                                   let uu____3021 =
                                     let uu____3022 =
                                       let uu____3029 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3029, [prefix; x1])  in
                                     FStar_Parser_AST.Op uu____3022  in
                                   mk uu____3021  in
                                 FStar_Pervasives_Native.Some uu____3020))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3033) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last args1  in
               let body =
                 match args2 with
                 | (b,uu____3059)::[] -> b
                 | uu____3076 -> failwith "wrong arguments to dtuple"  in
               let uu____3086 =
                 let uu____3087 = FStar_Syntax_Subst.compress body  in
                 uu____3087.FStar_Syntax_Syntax.n  in
               (match uu____3086 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3092) ->
                    let uu____3117 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3117 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3127 = FStar_Options.print_implicits ()
                              in
                           if uu____3127 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3144 =
                           let uu____3145 =
                             let uu____3156 =
                               FStar_List.map
                                 (fun uu____3167  ->
                                    FStar_Util.Inl uu____3167) xs3
                                in
                             (uu____3156, body3)  in
                           FStar_Parser_AST.Sum uu____3145  in
                         mk uu____3144)
                | uu____3174 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3197  ->
                              match uu____3197 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3215) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3224) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3233 = FStar_List.hd args1  in
               (match uu____3233 with
                | (t1,uu____3247) ->
                    let uu____3252 =
                      let uu____3253 = FStar_Syntax_Subst.compress t1  in
                      uu____3253.FStar_Syntax_Syntax.n  in
                    (match uu____3252 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3260 =
                           let uu____3261 =
                             let uu____3266 = resugar_term' env t1  in
                             (uu____3266, f)  in
                           FStar_Parser_AST.Project uu____3261  in
                         mk uu____3260
                     | uu____3267 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3268) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___426_3295  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3305 =
                           match new_args with
                           | (a1,uu____3315)::(a2,uu____3317)::[] -> (a1, a2)
                           | uu____3344 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3305 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3366 =
                                  let uu____3367 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3367.FStar_Syntax_Syntax.n  in
                                match uu____3366 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3372) ->
                                    let uu____3397 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3397 with | (x1,e2) -> e2)
                                | uu____3404 ->
                                    let uu____3405 =
                                      let uu____3407 =
                                        let uu____3409 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3409
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3407
                                       in
                                    failwith uu____3405
                                 in
                              let body1 =
                                let uu____3412 = decomp body  in
                                resugar_term' env uu____3412  in
                              let handler1 =
                                let uu____3414 = decomp handler  in
                                resugar_term' env uu____3414  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3422,uu____3423,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3455,uu____3456,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3493 =
                                      let uu____3494 =
                                        let uu____3503 = resugar_body t11  in
                                        (uu____3503, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3494
                                       in
                                    mk uu____3493
                                | uu____3506 ->
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
                                | uu____3564 -> []  in
                              let branches = resugar_branches handler1  in
                              mk (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3597 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3598) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3607) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3630) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3695,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3727,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3758 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3771 =
                   let uu____3772 = FStar_Syntax_Subst.compress body  in
                   uu____3772.FStar_Syntax_Syntax.n  in
                 match uu____3771 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3777) ->
                     let uu____3802 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3802 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3812 = FStar_Options.print_implicits ()
                               in
                            if uu____3812 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3828 =
                            let uu____3837 =
                              let uu____3838 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3838.FStar_Syntax_Syntax.n  in
                            match uu____3837 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3856 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3873,pats) ->
                                      let uu____3907 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3951  ->
                                                     match uu____3951 with
                                                     | (e2,uu____3959) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3907, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3975 =
                                        mk
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3975)
                                  | uu____3984 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3856 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4016 ->
                                let uu____4017 = resugar_term' env body2  in
                                ([], uu____4017)
                             in
                          (match uu____3828 with
                           | (pats,body3) ->
                               let uu____4034 = uncurry xs3 pats body3  in
                               (match uu____4034 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4065 =
                                        let uu____4066 =
                                          let uu____4085 =
                                            let uu____4096 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4096, pats1)  in
                                          (xs4, uu____4085, body4)  in
                                        FStar_Parser_AST.QForall uu____4066
                                         in
                                      mk uu____4065
                                    else
                                      (let uu____4119 =
                                         let uu____4120 =
                                           let uu____4139 =
                                             let uu____4150 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4150, pats1)  in
                                           (xs4, uu____4139, body4)  in
                                         FStar_Parser_AST.QExists uu____4120
                                          in
                                       mk uu____4119))))
                 | uu____4171 ->
                     if op = "forall"
                     then
                       let uu____4175 =
                         let uu____4176 =
                           let uu____4195 = resugar_term' env body  in
                           ([], ([], []), uu____4195)  in
                         FStar_Parser_AST.QForall uu____4176  in
                       mk uu____4175
                     else
                       (let uu____4218 =
                          let uu____4219 =
                            let uu____4238 = resugar_term' env body  in
                            ([], ([], []), uu____4238)  in
                          FStar_Parser_AST.QExists uu____4219  in
                        mk uu____4218)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last args1  in
                 (match args2 with
                  | (b,uu____4277)::[] -> resugar_forall_body b
                  | uu____4294 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4306) ->
               let uu____4314 = FStar_List.hd args1  in
               (match uu____4314 with
                | (e1,uu____4328) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity1) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4400  ->
                         match uu____4400 with
                         | (e1,qual) ->
                             let uu____4417 = resugar_term' env e1  in
                             let uu____4418 = resugar_imp env qual  in
                             (uu____4417, uu____4418)))
                  in
               (match expected_arity1 with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4434 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4434 with
                       | (op_args,rest) ->
                           let head =
                             let uu____4482 =
                               let uu____4483 =
                                 let uu____4490 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4490)  in
                               FStar_Parser_AST.Op uu____4483  in
                             mk uu____4482  in
                           FStar_List.fold_left
                             (fun head1  ->
                                fun uu____4508  ->
                                  match uu____4508 with
                                  | (arg,qual) ->
                                      mk
                                        (FStar_Parser_AST.App
                                           (head1, arg, qual))) head rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n when
                    (FStar_List.length args1) = n ->
                    let uu____4527 =
                      let uu____4528 =
                        let uu____4535 =
                          let uu____4538 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4538
                           in
                        (op1, uu____4535)  in
                      FStar_Parser_AST.Op uu____4528  in
                    mk uu____4527
                | uu____4551 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4620 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4620 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4666 =
                   let uu____4679 =
                     let uu____4684 = resugar_pat' env pat1 branch_bv  in
                     let uu____4685 = resugar_term' env e  in
                     (uu____4684, uu____4685)  in
                   (FStar_Pervasives_Native.None, uu____4679)  in
                 [uu____4666]  in
               let body = resugar_term' env t2  in
               mk
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4737,t1)::(pat2,uu____4740,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4836 =
            let uu____4837 =
              let uu____4844 = resugar_term' env e  in
              let uu____4845 = resugar_term' env t1  in
              let uu____4846 = resugar_term' env t2  in
              (uu____4844, uu____4845, uu____4846)  in
            FStar_Parser_AST.If uu____4837  in
          mk uu____4836
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4912 =
            match uu____4912 with
            | (pat,wopt,b) ->
                let uu____4954 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4954 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5006 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5006
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5010 =
            let uu____5011 =
              let uu____5026 = resugar_term' env e  in
              let uu____5027 = FStar_List.map resugar_branch branches  in
              (uu____5026, uu____5027)  in
            FStar_Parser_AST.Match uu____5011  in
          mk uu____5010
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5073) ->
          let term =
            match asc with
            | FStar_Util.Inl n -> resugar_term' env n
            | FStar_Util.Inr n -> resugar_comp' env n  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5142 =
            let uu____5143 =
              let uu____5152 = resugar_term' env e  in
              (uu____5152, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5143  in
          mk uu____5142
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5181 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5181 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5235 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5235
                    in
                 let uu____5242 =
                   let uu____5247 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5247
                    in
                 match uu____5242 with
                 | (univs,td) ->
                     let uu____5267 =
                       let uu____5274 =
                         let uu____5275 = FStar_Syntax_Subst.compress td  in
                         uu____5275.FStar_Syntax_Syntax.n  in
                       match uu____5274 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5284,(t1,uu____5286)::(d,uu____5288)::[])
                           -> (t1, d)
                       | uu____5345 -> failwith "wrong let binding format"
                        in
                     (match uu____5267 with
                      | (typ,def) ->
                          let uu____5376 =
                            let uu____5392 =
                              let uu____5393 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5393.FStar_Syntax_Syntax.n  in
                            match uu____5392 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5413) ->
                                let uu____5438 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5438 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5469 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5469
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5492 -> ([], def, false)  in
                          (match uu____5376 with
                           | (binders,term,is_pat_app) ->
                               let uu____5547 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5558 =
                                       let uu____5559 =
                                         let uu____5560 =
                                           let uu____5567 =
                                             bv_as_unique_ident bv  in
                                           (uu____5567,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5560
                                          in
                                       mk_pat uu____5559  in
                                     (uu____5558, term)
                                  in
                               (match uu____5547 with
                                | (pat,term1) ->
                                    let uu____5589 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5632  ->
                                                  match uu____5632 with
                                                  | (bv,q) ->
                                                      let uu____5647 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5647
                                                        (fun q1  ->
                                                           let uu____5659 =
                                                             let uu____5660 =
                                                               let uu____5667
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5667,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5660
                                                              in
                                                           mk_pat uu____5659)))
                                           in
                                        let uu____5670 =
                                          let uu____5675 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5675)
                                           in
                                        let uu____5678 =
                                          universe_to_string univs  in
                                        (uu____5670, uu____5678)
                                      else
                                        (let uu____5687 =
                                           let uu____5692 =
                                             resugar_term' env term1  in
                                           (pat, uu____5692)  in
                                         let uu____5693 =
                                           universe_to_string univs  in
                                         (uu____5687, uu____5693))
                                       in
                                    (attrs_opt, uu____5589))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5799 =
                   match uu____5799 with
                   | (attrs,(pb,univs)) ->
                       let uu____5859 =
                         let uu____5861 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5861  in
                       if uu____5859
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5942) ->
          let s =
            let uu____5961 =
              let uu____5963 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5963 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5961  in
          let uu____5968 = mk FStar_Parser_AST.Wild  in label s uu____5968
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5976 =
            let uu____5977 =
              let uu____5982 = resugar_term' env tm  in (uu____5982, qi1)  in
            FStar_Parser_AST.Quote uu____5977  in
          mk uu____5976
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_5994 =
            match uu___4_5994 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6002,(uu____6003,(p,t11))::[],t2) ->
                      mk (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6064 =
                        let uu____6065 =
                          let uu____6074 = resugar_seq t11  in
                          (uu____6074, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6065  in
                      mk uu____6064
                  | uu____6077 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6078,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6142  ->
                         match uu____6142 with
                         | (x,uu____6150) -> resugar_term' env x))
                  in
               mk (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6155 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6166,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6172,uu____6173,t1)
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
               let uu____6213 = FStar_Options.print_universes ()  in
               if uu____6213
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
               let uu____6277 = FStar_Options.print_universes ()  in
               if uu____6277
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
            let uu____6321 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6321, FStar_Parser_AST.Nothing)  in
          let uu____6322 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6322
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6345 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6345
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6430 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6430, (FStar_Pervasives_Native.snd post))  in
                    let uu____6441 =
                      let uu____6450 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6450 then [] else [pre]  in
                    let uu____6485 =
                      let uu____6494 =
                        let uu____6503 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6503 then [] else [pats]  in
                      FStar_List.append [post1] uu____6494  in
                    FStar_List.append uu____6441 uu____6485
                | uu____6562 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6596  ->
                   match uu____6596 with
                   | (e,uu____6608) ->
                       let uu____6613 = resugar_term' env e  in
                       (uu____6613, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_6638 =
              match uu___5_6638 with
              | [] -> l
              | hd::tl ->
                  (match hd with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6671 = resugar_term' env e  in
                         (uu____6671, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl
                   | uu____6676 -> aux l tl)
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
        let uu____6723 = b  in
        match uu____6723 with
        | (x,aq) ->
            let uu____6732 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6732
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6746 =
                       let uu____6747 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6747  in
                     FStar_Parser_AST.mk_binder uu____6746 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6748 ->
                     let uu____6749 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6749
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6754 =
                          let uu____6755 =
                            let uu____6760 = bv_as_unique_ident x  in
                            (uu____6760, e)  in
                          FStar_Parser_AST.Annotated uu____6755  in
                        FStar_Parser_AST.mk_binder uu____6754 r
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
              let uu____6780 = FStar_Syntax_Syntax.range_of_bv v  in
              FStar_Parser_AST.mk_pattern a uu____6780  in
            let used = FStar_Util.set_mem v body_bv  in
            let pat =
              let uu____6784 =
                if used
                then
                  let uu____6786 =
                    let uu____6793 = bv_as_unique_ident v  in
                    (uu____6793, aqual)  in
                  FStar_Parser_AST.PatVar uu____6786
                else FStar_Parser_AST.PatWild aqual  in
              mk uu____6784  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6800;
                  FStar_Syntax_Syntax.vars = uu____6801;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6811 = FStar_Options.print_bound_var_types ()  in
                if uu____6811
                then
                  let uu____6814 =
                    let uu____6815 =
                      let uu____6826 =
                        let uu____6833 = resugar_term' env typ  in
                        (uu____6833, FStar_Pervasives_Native.None)  in
                      (pat, uu____6826)  in
                    FStar_Parser_AST.PatAscribed uu____6815  in
                  mk uu____6814
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
          let uu____6854 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6854
            (fun aqual  ->
               let uu____6866 =
                 let uu____6871 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun uu____6882  ->
                      FStar_Pervasives_Native.Some uu____6882) uu____6871
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6866)

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
          (let uu____6944 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6944) &&
            (let uu____6947 =
               FStar_List.existsML
                 (fun uu____6960  ->
                    match uu____6960 with
                    | (pattern,is_implicit) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6982)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6987 -> false
                          | uu____6989 -> true  in
                        is_implicit && might_be_used) args
                in
             Prims.op_Negation uu____6947)
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
            let uu____7057 = may_drop_implicits args  in
            if uu____7057 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7082  ->
                 match uu____7082 with
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
              ((let uu____7137 =
                  let uu____7139 =
                    let uu____7141 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7141  in
                  Prims.op_Negation uu____7139  in
                if uu____7137
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
              let uu____7185 = filter_pattern_imp args  in
              (match uu____7185 with
               | (hd,false )::(tl,false )::[] ->
                   let hd' = aux hd (FStar_Pervasives_Native.Some false)  in
                   let uu____7235 =
                     aux tl (FStar_Pervasives_Native.Some false)  in
                   (match uu____7235 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7254 =
                       let uu____7260 =
                         let uu____7262 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7262
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7260)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7254);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7315  ->
                        match uu____7315 with
                        | (p2,is_implicit) ->
                            if is_implicit
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7332 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7332)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7340;
                 FStar_Syntax_Syntax.fv_delta = uu____7341;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7370 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7370 FStar_List.rev  in
              let args1 =
                let uu____7386 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7406  ->
                          match uu____7406 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7386 FStar_List.rev  in
              let rec map2 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd::tl) -> []
                | (hd::tl,[]) ->
                    let uu____7484 = map2 tl []  in
                    (hd,
                      (mk
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7484
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7507 = map2 tl1 tl2  in (hd1, hd2) ::
                      uu____7507
                 in
              let args2 =
                let uu____7525 = map2 fields1 args1  in
                FStar_All.pipe_right uu____7525 FStar_List.rev  in
              mk (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v ->
              let uu____7569 =
                string_to_op
                  (v.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7569 with
               | FStar_Pervasives_Native.Some (op,uu____7581) ->
                   let uu____7598 =
                     let uu____7599 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7599  in
                   mk uu____7598
               | FStar_Pervasives_Native.None  ->
                   let uu____7609 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v uu____7609 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7614 ->
              let uu____7615 =
                let uu____7616 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7616  in
              mk uu____7615
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
          let uu____7656 =
            let uu____7659 =
              let uu____7660 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7660  in
            FStar_Pervasives_Native.Some uu____7659  in
          FStar_Pervasives_Native.Some uu____7656

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
          let uu____7672 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7672

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_7680  ->
    match uu___6_7680 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7687 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7688 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7689 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7694 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7703 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7712 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_7718  ->
    match uu___7_7718 with
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
            (tylid,uvs,bs,t,uu____7761,datacons) ->
            let uu____7771 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7799,uu____7800,uu____7801,inductive_lid,uu____7803,uu____7804)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7811 -> failwith "unexpected"))
               in
            (match uu____7771 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7832 = FStar_Options.print_implicits ()  in
                   if uu____7832 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7849 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_7856  ->
                             match uu___8_7856 with
                             | FStar_Syntax_Syntax.RecordType uu____7858 ->
                                 true
                             | uu____7868 -> false))
                      in
                   if uu____7849
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7906,univs,term,uu____7909,num,uu____7911)
                           ->
                           let uu____7918 =
                             let uu____7919 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7919.FStar_Syntax_Syntax.n  in
                           (match uu____7918 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7929)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7986  ->
                                          match uu____7986 with
                                          | (b,qual) ->
                                              let uu____8003 =
                                                bv_as_unique_ident b  in
                                              let uu____8004 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8003, uu____8004)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8009 -> failwith "unexpected")
                       | uu____8017 -> failwith "unexpected"  in
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
                            (l,univs,term,uu____8112,num,uu____8114) ->
                            let c =
                              let uu____8131 =
                                let uu____8134 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8134  in
                              ((l.FStar_Ident.ident), uu____8131, false)  in
                            c :: constructors
                        | uu____8148 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8208 ->
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
        let uu____8234 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8234;
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
        let uu____8264 = ts  in
        match uu____8264 with
        | (univs,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8277 =
              let uu____8278 =
                let uu____8289 =
                  let uu____8292 =
                    let uu____8293 =
                      let uu____8306 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____8306)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____8293  in
                  [uu____8292]  in
                (false, false, uu____8289)  in
              FStar_Parser_AST.Tycon uu____8278  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8277
  
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
              let uu____8371 = resugar_tscheme'' env name ts  in [uu____8371]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8389 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____8391 =
             let uu____8394 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____8396 =
               let uu____8399 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____8401 =
                 let uu____8404 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____8406 =
                   let uu____8409 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____8411 =
                     let uu____8414 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____8416 =
                       let uu____8419 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____8419 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____8414 :: uu____8416  in
                   uu____8409 :: uu____8411  in
                 uu____8404 :: uu____8406  in
               uu____8399 :: uu____8401  in
             uu____8394 :: uu____8396  in
           uu____8389 :: uu____8391)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____8449 =
        match uu____8449 with
        | (ts,uu____8456) -> resugar_tscheme'' env name ts  in
      let uu____8457 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____8459 =
        let uu____8462 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____8464 =
          let uu____8467 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____8469 =
            let uu____8472 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____8474 =
              let uu____8477 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____8477]  in
            uu____8472 :: uu____8474  in
          uu____8467 :: uu____8469  in
        uu____8462 :: uu____8464  in
      uu____8457 :: uu____8459
  
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
            let uu____8538 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____8538 with
            | (bs,action_defn) ->
                let uu____8545 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____8545 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____8555 = FStar_Options.print_implicits ()  in
                       if uu____8555
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____8565 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____8565 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____8582 =
                           let uu____8593 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____8593,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____8582  in
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
          let uu____8637 =
            let uu____8642 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____8642
             in
          match uu____8637 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____8660 = FStar_Options.print_implicits ()  in
                if uu____8660 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____8670 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____8670 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8720) ->
          let uu____8729 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8752 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8770 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8778 -> false
                    | uu____8795 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8729 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8833 se1 =
                 match uu____8833 with
                 | (datacon_ses1,tycons) ->
                     let uu____8859 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8859 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8874 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8874 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8909 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____8909
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8920,uu____8921,uu____8922,uu____8923,uu____8924)
                              ->
                              let uu____8931 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8931
                          | uu____8934 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8938 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____8944 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8958) ->
          let uu____8963 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_8971  ->
                    match uu___9_8971 with
                    | FStar_Syntax_Syntax.Projector (uu____8973,uu____8974)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8976 -> true
                    | uu____8978 -> false))
             in
          if uu____8963
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
             | FStar_Parser_AST.Let (isrec,lets,uu____9013) ->
                 let uu____9042 =
                   let uu____9043 =
                     let uu____9044 =
                       let uu____9055 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9055)  in
                     FStar_Parser_AST.TopLevelLet uu____9044  in
                   decl'_to_decl se uu____9043  in
                 FStar_Pervasives_Native.Some uu____9042
             | uu____9092 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9097,fml) ->
          let uu____9099 =
            let uu____9100 =
              let uu____9101 =
                let uu____9106 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9106)  in
              FStar_Parser_AST.Assume uu____9101  in
            decl'_to_decl se uu____9100  in
          FStar_Pervasives_Native.Some uu____9099
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9108 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9108
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9117,t) ->
                let uu____9127 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9127
            | uu____9128 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9136,t) ->
                let uu____9146 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9146
            | uu____9147 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9171 -> failwith "Should not happen hopefully"  in
          let uu____9181 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9181
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9191 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9191 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9203 = FStar_Options.print_implicits ()  in
                 if uu____9203 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9219 =
                 let uu____9220 =
                   let uu____9221 =
                     let uu____9232 =
                       let uu____9235 =
                         let uu____9236 =
                           let uu____9249 = resugar_comp' env c1  in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____9249)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____9236  in
                       [uu____9235]  in
                     (false, false, uu____9232)  in
                   FStar_Parser_AST.Tycon uu____9221  in
                 decl'_to_decl se uu____9220  in
               FStar_Pervasives_Native.Some uu____9219)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9261 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9261
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9265 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9273  ->
                    match uu___10_9273 with
                    | FStar_Syntax_Syntax.Projector (uu____9275,uu____9276)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9278 -> true
                    | uu____9280 -> false))
             in
          if uu____9265
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9288 =
                 (let uu____9292 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9292) || (FStar_List.isEmpty uvs)
                  in
               if uu____9288
               then resugar_term' env t
               else
                 (let uu____9297 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9297 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9306 = resugar_term' env t1  in
                      label universes uu____9306)
                in
             let uu____9307 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9307)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9314 =
            let uu____9315 =
              let uu____9316 =
                let uu____9323 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9328 = resugar_term' env t  in
                (uu____9323, uu____9328)  in
              FStar_Parser_AST.Splice uu____9316  in
            decl'_to_decl se uu____9315  in
          FStar_Pervasives_Native.Some uu____9314
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9331 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9348 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9364 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n,p,(uu____9368,t),uu____9370) ->
          let uu____9379 =
            let uu____9380 =
              let uu____9381 =
                let uu____9390 = resugar_term' env t  in
                (m, n, p, uu____9390)  in
              FStar_Parser_AST.Polymonadic_bind uu____9381  in
            decl'_to_decl se uu____9380  in
          FStar_Pervasives_Native.Some uu____9379
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9414 = noenv resugar_term'  in uu____9414 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9432 = noenv resugar_sigelt'  in uu____9432 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9450 = noenv resugar_comp'  in uu____9450 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9473 = noenv resugar_pat'  in uu____9473 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9507 = noenv resugar_binder'  in uu____9507 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9532 = noenv resugar_tscheme'  in uu____9532 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____9560 = noenv resugar_eff_decl'  in uu____9560 r q ed
  