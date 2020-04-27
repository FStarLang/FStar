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
  
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Util.tts t 
let map_opt :
  'uuuuuu41 'uuuuuu42 .
    unit ->
      ('uuuuuu41 -> 'uuuuuu42 FStar_Pervasives_Native.option) ->
        'uuuuuu41 Prims.list -> 'uuuuuu42 Prims.list
  = fun uu____59  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____68 =
        (let uu____72 = FStar_Ident.text_of_id x.FStar_Syntax_Syntax.ppname
            in
         FStar_Util.starts_with FStar_Ident.reserved_prefix uu____72) ||
          (FStar_Options.print_real_names ())
         in
      if uu____68
      then
        let uu____76 = FStar_Ident.text_of_id x.FStar_Syntax_Syntax.ppname
           in
        let uu____78 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat uu____76 uu____78
      else FStar_Ident.text_of_id x.FStar_Syntax_Syntax.ppname  in
    let uu____82 =
      let uu____88 = FStar_Ident.range_of_id x.FStar_Syntax_Syntax.ppname  in
      (unique_name, uu____88)  in
    FStar_Ident.mk_ident uu____82
  
let filter_imp :
  'uuuuuu95 .
    ('uuuuuu95 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu95 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_150  ->
            match uu___0_150 with
            | (uu____158,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____165,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____166)) -> false
            | (uu____171,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____172)) -> false
            | uu____178 -> true))
  
let filter_pattern_imp :
  'uuuuuu191 .
    ('uuuuuu191 * Prims.bool) Prims.list ->
      ('uuuuuu191 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____226  ->
         match uu____226 with
         | (uu____233,is_implicit) -> Prims.op_Negation is_implicit) xs
  
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
      | uu____283 -> (n, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs  ->
    let uu____296 = FStar_Options.print_universes ()  in
    if uu____296
    then
      let uu____300 =
        FStar_List.map (fun x  -> FStar_Ident.text_of_id x) univs  in
      FStar_All.pipe_right uu____300 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____349 ->
          let uu____350 = universe_to_int Prims.int_zero u  in
          (match uu____350 with
           | (n,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____361 =
                      let uu____362 =
                        let uu____363 =
                          let uu____375 = FStar_Util.string_of_int n  in
                          (uu____375, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____363  in
                      FStar_Parser_AST.Const uu____362  in
                    mk uu____361 r
                | uu____388 ->
                    let e1 =
                      let uu____390 =
                        let uu____391 =
                          let uu____392 =
                            let uu____404 = FStar_Util.string_of_int n  in
                            (uu____404, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____392  in
                        FStar_Parser_AST.Const uu____391  in
                      mk uu____390 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____418 =
                      let uu____419 =
                        let uu____426 = FStar_Ident.id_of_text "+"  in
                        (uu____426, [e1; e2])  in
                      FStar_Parser_AST.Op uu____419  in
                    mk uu____418 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____434 ->
               let t =
                 let uu____438 =
                   let uu____439 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____439  in
                 mk uu____438 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____448 =
                        let uu____449 =
                          let uu____456 = resugar_universe x r  in
                          (acc, uu____456, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____449  in
                      mk uu____448 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____458 -> mk FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____472 =
              let uu____478 =
                let uu____480 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____480  in
              (uu____478, r)  in
            FStar_Ident.mk_ident uu____472  in
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
    let name_of_op uu___1_534 =
      match uu___1_534 with
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
      | uu____862 -> FStar_Pervasives_Native.None  in
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
    | uu____1002 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____1020 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____1020 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1038 ->
               let maybeop =
                 let uu____1046 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1112)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1046
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
      (FStar_Parser_Const.salloc_lid, "alloc");
      (FStar_Parser_Const.calc_finish_lid, "calc_finish")]  in
    let fallback fv =
      let uu____1451 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1451 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1521 ->
          let length =
            let uu____1530 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____1530  in
          let str =
            if length = Prims.int_zero
            then
              FStar_Ident.string_of_lid
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            else
              (let uu____1540 =
                 FStar_Ident.string_of_lid
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_Util.substring_from uu____1540 (length + Prims.int_one))
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
                (let uu____1627 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1627
                 then
                   let uu____1640 =
                     let uu____1649 =
                       FStar_Ident.string_of_lid
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     (uu____1649, FStar_Pervasives_Native.None)  in
                   FStar_Pervasives_Native.Some uu____1640
                 else FStar_Pervasives_Native.None)
       in
    let uu____1674 =
      let uu____1675 = FStar_Syntax_Subst.compress t  in
      uu____1675.FStar_Syntax_Syntax.n  in
    match uu____1674 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length =
          let uu____1687 =
            FStar_Ident.nsstr
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_String.length uu____1687  in
        let s =
          if length = Prims.int_zero
          then
            FStar_Ident.string_of_lid
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          else
            (let uu____1697 =
               FStar_Ident.string_of_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.substring_from uu____1697 (length + Prims.int_one))
           in
        let uu____1700 = string_to_op s  in
        (match uu____1700 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1740 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1757 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1774 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1785 -> true
    | uu____1787 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let uu____1803 = FStar_Ident.string_of_lid lid  in
    match uu____1803 with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1810 ->
        let uu____1812 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1812
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1826 = may_shorten lid  in
      if uu____1826 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1981 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1981  in
      let uu____1984 =
        let uu____1985 = FStar_Syntax_Subst.compress t  in
        uu____1985.FStar_Syntax_Syntax.n  in
      match uu____1984 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1988 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____2005 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____2005
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____2008 =
              let uu____2009 = bv_as_unique_ident x  in [uu____2009]  in
            FStar_Ident.lid_of_ids uu____2008  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____2012 =
              let uu____2013 = bv_as_unique_ident x  in [uu____2013]  in
            FStar_Ident.lid_of_ids uu____2012  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length =
            let uu____2017 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____2017  in
          let s =
            if length = Prims.int_zero
            then FStar_Ident.string_of_lid a
            else
              (let uu____2027 = FStar_Ident.string_of_lid a  in
               FStar_Util.substring_from uu____2027 (length + Prims.int_one))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____2036 =
              let uu____2037 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____2037  in
            mk uu____2036
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
               | uu____2061 -> failwith "wrong projector format")
            else
              (let uu____2068 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2068
               then
                 let uu____2071 =
                   let uu____2072 =
                     let uu____2073 =
                       let uu____2079 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2079)  in
                     FStar_Ident.mk_ident uu____2073  in
                   FStar_Parser_AST.Tvar uu____2072  in
                 mk uu____2071
               else
                 (let uu____2084 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2084
                  then
                    let uu____2087 =
                      let uu____2088 =
                        let uu____2089 =
                          let uu____2095 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2095)  in
                        FStar_Ident.mk_ident uu____2089  in
                      FStar_Parser_AST.Tvar uu____2088  in
                    mk uu____2087
                  else
                    (let uu____2100 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2104 =
                            let uu____2106 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2106  in
                          let uu____2109 = FStar_String.get s Prims.int_zero
                             in
                          uu____2104 <> uu____2109)
                        in
                     if uu____2100
                     then
                       let uu____2114 =
                         let uu____2115 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2115  in
                       mk uu____2114
                     else
                       (let uu____2118 =
                          let uu____2119 =
                            let uu____2130 = maybe_shorten_fv env fv  in
                            (uu____2130, [])  in
                          FStar_Parser_AST.Construct uu____2119  in
                        mk uu____2118))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2148 = FStar_Options.print_universes ()  in
          if uu____2148
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
                   let uu____2179 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs
                      in
                   FStar_List.append args uu____2179  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd, args1)) r l
             | uu____2202 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2210 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2210
          then
            let uu____2213 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk uu____2213
          else mk (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2218 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2239 -> ("Type", true)  in
          (match uu____2218 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2251 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk uu____2251  in
               let uu____2252 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2252
               then
                 let uu____2255 =
                   let uu____2256 =
                     let uu____2263 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2263, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2256  in
                 mk uu____2255
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2268) ->
          let uu____2293 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2293 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2309 = FStar_Options.print_implicits ()  in
                 if uu____2309 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2347  ->
                         match uu____2347 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2387 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2387 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2397 = FStar_Options.print_implicits ()  in
                 if uu____2397 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2408 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2408 FStar_List.rev  in
               let rec aux body3 uu___2_2433 =
                 match uu___2_2433 with
                 | [] -> body3
                 | hd::tl ->
                     let body4 = mk (FStar_Parser_AST.Product ([hd], body3))
                        in
                     aux body4 tl
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2449 =
            let uu____2454 =
              let uu____2455 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2455]  in
            FStar_Syntax_Subst.open_term uu____2454 phi  in
          (match uu____2449 with
           | (x1,phi1) ->
               let b =
                 let uu____2477 =
                   let uu____2480 = FStar_List.hd x1  in
                   resugar_binder' env uu____2480 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2477  in
               let uu____2487 =
                 let uu____2488 =
                   let uu____2493 = resugar_term' env phi1  in
                   (b, uu____2493)  in
                 FStar_Parser_AST.Refine uu____2488  in
               mk uu____2487)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2495;
             FStar_Syntax_Syntax.vars = uu____2496;_},(e,uu____2498)::[])
          when
          (let uu____2539 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2539) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last uu___3_2588 =
            match uu___3_2588 with
            | hd::[] -> [hd]
            | hd::tl -> last tl
            | uu____2658 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2744,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2745))::tl ->
                  drop_implicits tl
              | uu____2764 -> args2  in
            let uu____2773 = drop_implicits args1  in
            match uu____2773 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2805::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2835 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2935  ->
                   match uu____2935 with
                   | (e2,qual) ->
                       let uu____2952 = resugar_term' env e2  in
                       let uu____2953 = resugar_imp env qual  in
                       (uu____2952, uu____2953)) args1
               in
            let uu____2954 = resugar_term' env e1  in
            match uu____2954 with
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
                     fun uu____2991  ->
                       match uu____2991 with
                       | (x,qual) -> mk (FStar_Parser_AST.App (acc, x, qual)))
                  e2 args2
             in
          let args1 =
            let uu____3007 = FStar_Options.print_implicits ()  in
            if uu____3007 then args else filter_imp args  in
          let uu____3022 = resugar_term_as_op e  in
          (match uu____3022 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("calc_finish",uu____3035) ->
               let uu____3043 = resugar_calc env t  in
               (match uu____3043 with
                | FStar_Pervasives_Native.Some r -> r
                | uu____3047 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("tuple",uu____3050) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____3075  ->
                        match uu____3075 with
                        | (x,uu____3087) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix ->
                                 let uu____3096 =
                                   let uu____3097 =
                                     let uu____3098 =
                                       let uu____3105 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3105, [prefix; x1])  in
                                     FStar_Parser_AST.Op uu____3098  in
                                   mk uu____3097  in
                                 FStar_Pervasives_Native.Some uu____3096))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3109) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last args1  in
               let body =
                 match args2 with
                 | (b,uu____3135)::[] -> b
                 | uu____3152 -> failwith "wrong arguments to dtuple"  in
               let uu____3162 =
                 let uu____3163 = FStar_Syntax_Subst.compress body  in
                 uu____3163.FStar_Syntax_Syntax.n  in
               (match uu____3162 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3168) ->
                    let uu____3193 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3193 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3203 = FStar_Options.print_implicits ()
                              in
                           if uu____3203 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3220 =
                           let uu____3221 =
                             let uu____3232 =
                               FStar_List.map
                                 (fun uu____3243  ->
                                    FStar_Util.Inl uu____3243) xs3
                                in
                             (uu____3232, body3)  in
                           FStar_Parser_AST.Sum uu____3221  in
                         mk uu____3220)
                | uu____3250 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3273  ->
                              match uu____3273 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3291) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3300) when
               let uu____3308 =
                 FStar_Ident.string_of_lid FStar_Parser_Const.sread_lid  in
               ref_read = uu____3308 ->
               let uu____3311 = FStar_List.hd args1  in
               (match uu____3311 with
                | (t1,uu____3325) ->
                    let uu____3330 =
                      let uu____3331 = FStar_Syntax_Subst.compress t1  in
                      uu____3331.FStar_Syntax_Syntax.n  in
                    (match uu____3330 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         let uu____3335 =
                           FStar_Ident.string_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Util.field_projector_contains_constructor
                           uu____3335
                         ->
                         let f =
                           let uu____3338 =
                             let uu____3339 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             [uu____3339]  in
                           FStar_Ident.lid_of_path uu____3338
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3343 =
                           let uu____3344 =
                             let uu____3349 = resugar_term' env t1  in
                             (uu____3349, f)  in
                           FStar_Parser_AST.Project uu____3344  in
                         mk uu____3343
                     | uu____3350 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3351) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___434_3378  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3388 =
                           match new_args with
                           | (a1,uu____3398)::(a2,uu____3400)::[] -> (a1, a2)
                           | uu____3427 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3388 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3449 =
                                  let uu____3450 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3450.FStar_Syntax_Syntax.n  in
                                match uu____3449 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3455) ->
                                    let uu____3480 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3480 with | (x1,e2) -> e2)
                                | uu____3487 ->
                                    let uu____3488 =
                                      let uu____3490 =
                                        let uu____3492 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3492
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3490
                                       in
                                    failwith uu____3488
                                 in
                              let body1 =
                                let uu____3495 = decomp body  in
                                resugar_term' env uu____3495  in
                              let handler1 =
                                let uu____3497 = decomp handler  in
                                resugar_term' env uu____3497  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3505,uu____3506,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3538,uu____3539,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3576 =
                                      let uu____3577 =
                                        let uu____3586 = resugar_body t11  in
                                        (uu____3586, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3577
                                       in
                                    mk uu____3576
                                | uu____3589 ->
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
                                | uu____3647 -> []  in
                              let branches = resugar_branches handler1  in
                              mk (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3680 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3681) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3690) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3713) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3778,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3810,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3841 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3854 =
                   let uu____3855 = FStar_Syntax_Subst.compress body  in
                   uu____3855.FStar_Syntax_Syntax.n  in
                 match uu____3854 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3860) ->
                     let uu____3885 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3885 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3895 = FStar_Options.print_implicits ()
                               in
                            if uu____3895 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3911 =
                            let uu____3920 =
                              let uu____3921 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3921.FStar_Syntax_Syntax.n  in
                            match uu____3920 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3939 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3956,pats) ->
                                      let uu____3990 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____4034  ->
                                                     match uu____4034 with
                                                     | (e2,uu____4042) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3990, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____4058 =
                                        mk
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____4058)
                                  | uu____4067 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3939 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4099 ->
                                let uu____4100 = resugar_term' env body2  in
                                ([], uu____4100)
                             in
                          (match uu____3911 with
                           | (pats,body3) ->
                               let uu____4117 = uncurry xs3 pats body3  in
                               (match uu____4117 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4148 =
                                        let uu____4149 =
                                          let uu____4168 =
                                            let uu____4179 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4179, pats1)  in
                                          (xs4, uu____4168, body4)  in
                                        FStar_Parser_AST.QForall uu____4149
                                         in
                                      mk uu____4148
                                    else
                                      (let uu____4202 =
                                         let uu____4203 =
                                           let uu____4222 =
                                             let uu____4233 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4233, pats1)  in
                                           (xs4, uu____4222, body4)  in
                                         FStar_Parser_AST.QExists uu____4203
                                          in
                                       mk uu____4202))))
                 | uu____4254 ->
                     if op = "forall"
                     then
                       let uu____4258 =
                         let uu____4259 =
                           let uu____4278 = resugar_term' env body  in
                           ([], ([], []), uu____4278)  in
                         FStar_Parser_AST.QForall uu____4259  in
                       mk uu____4258
                     else
                       (let uu____4301 =
                          let uu____4302 =
                            let uu____4321 = resugar_term' env body  in
                            ([], ([], []), uu____4321)  in
                          FStar_Parser_AST.QExists uu____4302  in
                        mk uu____4301)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last args1  in
                 (match args2 with
                  | (b,uu____4360)::[] -> resugar_forall_body b
                  | uu____4377 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4389) ->
               let uu____4397 = FStar_List.hd args1  in
               (match uu____4397 with
                | (e1,uu____4411) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity1) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4483  ->
                         match uu____4483 with
                         | (e1,qual) ->
                             let uu____4500 = resugar_term' env e1  in
                             let uu____4501 = resugar_imp env qual  in
                             (uu____4500, uu____4501)))
                  in
               (match expected_arity1 with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4517 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4517 with
                       | (op_args,rest) ->
                           let head =
                             let uu____4565 =
                               let uu____4566 =
                                 let uu____4573 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4573)  in
                               FStar_Parser_AST.Op uu____4566  in
                             mk uu____4565  in
                           FStar_List.fold_left
                             (fun head1  ->
                                fun uu____4591  ->
                                  match uu____4591 with
                                  | (arg,qual) ->
                                      mk
                                        (FStar_Parser_AST.App
                                           (head1, arg, qual))) head rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n when
                    (FStar_List.length args1) = n ->
                    let uu____4610 =
                      let uu____4611 =
                        let uu____4618 =
                          let uu____4621 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4621
                           in
                        (op1, uu____4618)  in
                      FStar_Parser_AST.Op uu____4611  in
                    mk uu____4610
                | uu____4634 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4703 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4703 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4749 =
                   let uu____4762 =
                     let uu____4767 = resugar_pat' env pat1 branch_bv  in
                     let uu____4768 = resugar_term' env e  in
                     (uu____4767, uu____4768)  in
                   (FStar_Pervasives_Native.None, uu____4762)  in
                 [uu____4749]  in
               let body = resugar_term' env t2  in
               mk
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4820,t1)::(pat2,uu____4823,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4919 =
            let uu____4920 =
              let uu____4927 = resugar_term' env e  in
              let uu____4928 = resugar_term' env t1  in
              let uu____4929 = resugar_term' env t2  in
              (uu____4927, uu____4928, uu____4929)  in
            FStar_Parser_AST.If uu____4920  in
          mk uu____4919
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4995 =
            match uu____4995 with
            | (pat,wopt,b) ->
                let uu____5037 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____5037 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5089 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5089
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5093 =
            let uu____5094 =
              let uu____5109 = resugar_term' env e  in
              let uu____5110 = FStar_List.map resugar_branch branches  in
              (uu____5109, uu____5110)  in
            FStar_Parser_AST.Match uu____5094  in
          mk uu____5093
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5156) ->
          let term =
            match asc with
            | FStar_Util.Inl n -> resugar_term' env n
            | FStar_Util.Inr n -> resugar_comp' env n  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5225 =
            let uu____5226 =
              let uu____5235 = resugar_term' env e  in
              (uu____5235, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5226  in
          mk uu____5225
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5264 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5264 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5318 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5318
                    in
                 let uu____5325 =
                   let uu____5330 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5330
                    in
                 match uu____5325 with
                 | (univs,td) ->
                     let uu____5350 =
                       let uu____5357 =
                         let uu____5358 = FStar_Syntax_Subst.compress td  in
                         uu____5358.FStar_Syntax_Syntax.n  in
                       match uu____5357 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5367,(t1,uu____5369)::(d,uu____5371)::[])
                           -> (t1, d)
                       | uu____5428 -> failwith "wrong let binding format"
                        in
                     (match uu____5350 with
                      | (typ,def) ->
                          let uu____5459 =
                            let uu____5475 =
                              let uu____5476 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5476.FStar_Syntax_Syntax.n  in
                            match uu____5475 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5496) ->
                                let uu____5521 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5521 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5552 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5552
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5575 -> ([], def, false)  in
                          (match uu____5459 with
                           | (binders,term,is_pat_app) ->
                               let uu____5630 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5641 =
                                       let uu____5642 =
                                         let uu____5643 =
                                           let uu____5650 =
                                             bv_as_unique_ident bv  in
                                           (uu____5650,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5643
                                          in
                                       mk_pat uu____5642  in
                                     (uu____5641, term)
                                  in
                               (match uu____5630 with
                                | (pat,term1) ->
                                    let uu____5672 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5715  ->
                                                  match uu____5715 with
                                                  | (bv,q) ->
                                                      let uu____5730 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5730
                                                        (fun q1  ->
                                                           let uu____5742 =
                                                             let uu____5743 =
                                                               let uu____5750
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5750,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5743
                                                              in
                                                           mk_pat uu____5742)))
                                           in
                                        let uu____5753 =
                                          let uu____5758 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5758)
                                           in
                                        let uu____5761 =
                                          universe_to_string univs  in
                                        (uu____5753, uu____5761)
                                      else
                                        (let uu____5770 =
                                           let uu____5775 =
                                             resugar_term' env term1  in
                                           (pat, uu____5775)  in
                                         let uu____5776 =
                                           universe_to_string univs  in
                                         (uu____5770, uu____5776))
                                       in
                                    (attrs_opt, uu____5672))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5882 =
                   match uu____5882 with
                   | (attrs,(pb,univs)) ->
                       let uu____5942 =
                         let uu____5944 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5944  in
                       if uu____5942
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____6025) ->
          let s =
            let uu____6044 =
              let uu____6046 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____6046 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____6044  in
          let uu____6051 = mk FStar_Parser_AST.Wild  in label s uu____6051
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____6059 =
            let uu____6060 =
              let uu____6065 = resugar_term' env tm  in (uu____6065, qi1)  in
            FStar_Parser_AST.Quote uu____6060  in
          mk uu____6059
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_6077 =
            match uu___4_6077 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6085,(uu____6086,(p,t11))::[],t2) ->
                      mk (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6147 =
                        let uu____6148 =
                          let uu____6157 = resugar_seq t11  in
                          (uu____6157, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6148  in
                      mk uu____6147
                  | uu____6160 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6161,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6225  ->
                         match uu____6225 with
                         | (x,uu____6233) -> resugar_term' env x))
                  in
               mk (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6238 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6249,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6255,uu____6256,t1)
               -> resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk FStar_Parser_AST.Wild

and (resugar_calc :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Parser_AST.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t0  ->
      let mk a =
        FStar_Parser_AST.mk_term a t0.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let resugar_calc_finish t =
        let uu____6290 = FStar_Syntax_Util.head_and_args t  in
        match uu____6290 with
        | (hd,args) ->
            let uu____6339 =
              let uu____6354 =
                let uu____6355 =
                  let uu____6358 = FStar_Syntax_Util.un_uinst hd  in
                  FStar_Syntax_Subst.compress uu____6358  in
                uu____6355.FStar_Syntax_Syntax.n  in
              (uu____6354, args)  in
            (match uu____6339 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6376,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____6377))::(rel,FStar_Pervasives_Native.None
                                                                 )::(uu____6379,FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____6380))::
                (uu____6381,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6382))::(pf,FStar_Pervasives_Native.None
                                                              )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_finish_lid
                 ->
                 let pf1 = FStar_Syntax_Util.unthunk pf  in
                 FStar_Pervasives_Native.Some (rel, pf1)
             | uu____6480 -> FStar_Pervasives_Native.None)
         in
      let un_eta_rel rel =
        let bv_eq_tm b t =
          let uu____6522 =
            let uu____6523 = FStar_Syntax_Subst.compress t  in
            uu____6523.FStar_Syntax_Syntax.n  in
          match uu____6522 with
          | FStar_Syntax_Syntax.Tm_name b' when
              FStar_Syntax_Syntax.bv_eq b b' -> true
          | uu____6529 -> false  in
        let uu____6531 =
          let uu____6532 = FStar_Syntax_Subst.compress rel  in
          uu____6532.FStar_Syntax_Syntax.n  in
        match uu____6531 with
        | FStar_Syntax_Syntax.Tm_abs (b1::b2::[],body,uu____6540) ->
            let uu____6587 = FStar_Syntax_Subst.open_term [b1; b2] body  in
            (match uu____6587 with
             | (b11::b21::[],body1) ->
                 let body2 = FStar_Syntax_Util.unascribe body1  in
                 let body3 =
                   let uu____6647 = FStar_Syntax_Util.unb2t body2  in
                   match uu____6647 with
                   | FStar_Pervasives_Native.Some body3 -> body3
                   | FStar_Pervasives_Native.None  -> body2  in
                 let uu____6651 =
                   let uu____6652 = FStar_Syntax_Subst.compress body3  in
                   uu____6652.FStar_Syntax_Syntax.n  in
                 (match uu____6651 with
                  | FStar_Syntax_Syntax.Tm_app (e,args) when
                      (FStar_List.length args) >= (Prims.of_int (2)) ->
                      (match FStar_List.rev args with
                       | (a1,FStar_Pervasives_Native.None )::(a2,FStar_Pervasives_Native.None
                                                              )::rest
                           ->
                           let uu____6743 =
                             (bv_eq_tm (FStar_Pervasives_Native.fst b11) a2)
                               &&
                               (bv_eq_tm (FStar_Pervasives_Native.fst b21) a1)
                              in
                           if uu____6743
                           then
                             let uu____6752 =
                               FStar_Syntax_Util.mk_app e
                                 (FStar_List.rev rest)
                                in
                             FStar_All.pipe_left
                               (fun uu____6763  ->
                                  FStar_Pervasives_Native.Some uu____6763)
                               uu____6752
                           else FStar_Pervasives_Native.Some rel
                       | uu____6766 -> FStar_Pervasives_Native.Some rel)
                  | uu____6777 -> FStar_Pervasives_Native.Some rel))
        | uu____6778 -> FStar_Pervasives_Native.Some rel  in
      let resugar_step pack =
        let uu____6805 = FStar_Syntax_Util.head_and_args pack  in
        match uu____6805 with
        | (hd,args) ->
            let uu____6858 =
              let uu____6873 =
                let uu____6874 =
                  let uu____6877 = FStar_Syntax_Util.un_uinst hd  in
                  FStar_Syntax_Subst.compress uu____6877  in
                uu____6874.FStar_Syntax_Syntax.n  in
              (uu____6873, args)  in
            (match uu____6858 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6899,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____6900))::(uu____6901,FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Syntax.Implicit
                                                                 uu____6902))::
                (uu____6903,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6904))::(rel,FStar_Pervasives_Native.None
                                                              )::(z,FStar_Pervasives_Native.None
                                                                  )::
                (pf,FStar_Pervasives_Native.None )::(j,FStar_Pervasives_Native.None
                                                     )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_step_lid
                 ->
                 let pf1 = FStar_Syntax_Util.unthunk pf  in
                 let j1 = FStar_Syntax_Util.unthunk j  in
                 FStar_Pervasives_Native.Some (z, rel, j1, pf1)
             | uu____7038 -> FStar_Pervasives_Native.None)
         in
      let resugar_init pack =
        let uu____7071 = FStar_Syntax_Util.head_and_args pack  in
        match uu____7071 with
        | (hd,args) ->
            let uu____7116 =
              let uu____7131 =
                let uu____7132 =
                  let uu____7135 = FStar_Syntax_Util.un_uinst hd  in
                  FStar_Syntax_Subst.compress uu____7135  in
                uu____7132.FStar_Syntax_Syntax.n  in
              (uu____7131, args)  in
            (match uu____7116 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____7149,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____7150))::(x,FStar_Pervasives_Native.None
                                                                 )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_init_lid
                 -> FStar_Pervasives_Native.Some x
             | uu____7199 -> FStar_Pervasives_Native.None)
         in
      let rec resugar_all_steps pack =
        let uu____7248 = resugar_step pack  in
        match uu____7248 with
        | FStar_Pervasives_Native.Some (t,r,j,k) ->
            let uu____7285 = resugar_all_steps k  in
            FStar_Util.bind_opt uu____7285
              (fun uu____7327  ->
                 match uu____7327 with
                 | (steps,k1) ->
                     FStar_Pervasives_Native.Some (((t, r, j) :: steps), k1))
        | FStar_Pervasives_Native.None  ->
            FStar_Pervasives_Native.Some ([], pack)
         in
      let resugar_rel rel =
        let rel1 =
          let uu____7439 = un_eta_rel rel  in
          match uu____7439 with
          | FStar_Pervasives_Native.Some rel1 -> rel1
          | FStar_Pervasives_Native.None  -> rel  in
        let fallback uu____7448 =
          let uu____7449 =
            let uu____7450 = resugar_term' env rel1  in
            FStar_Parser_AST.Paren uu____7450  in
          mk uu____7449  in
        let uu____7451 = FStar_Syntax_Util.head_and_args rel1  in
        match uu____7451 with
        | (hd,args) ->
            let uu____7494 =
              (FStar_Options.print_implicits ()) &&
                (FStar_List.existsb
                   (fun uu____7505  ->
                      match uu____7505 with
                      | (uu____7513,q) -> FStar_Syntax_Syntax.is_implicit q)
                   args)
               in
            if uu____7494
            then fallback ()
            else
              (let uu____7522 = resugar_term_as_op hd  in
               match uu____7522 with
               | FStar_Pervasives_Native.Some
                   (s,FStar_Pervasives_Native.None ) ->
                   let uu____7539 =
                     let uu____7540 =
                       let uu____7547 = FStar_Ident.id_of_text s  in
                       (uu____7547, [])  in
                     FStar_Parser_AST.Op uu____7540  in
                   mk uu____7539
               | FStar_Pervasives_Native.Some
                   (s,FStar_Pervasives_Native.Some uu____7559) when
                   uu____7559 = (Prims.of_int (2)) ->
                   let uu____7560 =
                     let uu____7561 =
                       let uu____7568 = FStar_Ident.id_of_text s  in
                       (uu____7568, [])  in
                     FStar_Parser_AST.Op uu____7561  in
                   mk uu____7560
               | uu____7571 -> fallback ())
         in
      let build_calc rel x0 steps =
        let r = resugar_term' env  in
        let uu____7616 =
          let uu____7617 =
            let uu____7626 = resugar_rel rel  in
            let uu____7627 = r x0  in
            let uu____7628 =
              FStar_List.map
                (fun uu____7642  ->
                   match uu____7642 with
                   | (z,rel1,j) ->
                       let uu____7652 =
                         let uu____7659 = resugar_rel rel1  in
                         let uu____7660 = r j  in
                         let uu____7661 = r z  in
                         (uu____7659, uu____7660, uu____7661)  in
                       FStar_Parser_AST.CalcStep uu____7652) steps
               in
            (uu____7626, uu____7627, uu____7628)  in
          FStar_Parser_AST.CalcProof uu____7617  in
        mk uu____7616  in
      let uu____7664 = resugar_calc_finish t0  in
      FStar_Util.bind_opt uu____7664
        (fun uu____7679  ->
           match uu____7679 with
           | (rel,pack) ->
               let uu____7688 = resugar_all_steps pack  in
               FStar_Util.bind_opt uu____7688
                 (fun uu____7719  ->
                    match uu____7719 with
                    | (steps,k) ->
                        let uu____7752 = resugar_init k  in
                        FStar_Util.bind_opt uu____7752
                          (fun x0  ->
                             let uu____7758 =
                               build_calc rel x0 (FStar_List.rev steps)  in
                             FStar_All.pipe_left
                               (fun uu____7767  ->
                                  FStar_Pervasives_Native.Some uu____7767)
                               uu____7758)))

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
               let uu____7802 = FStar_Options.print_universes ()  in
               if uu____7802
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
               let uu____7866 = FStar_Options.print_universes ()  in
               if uu____7866
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
            let uu____7910 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____7910, FStar_Parser_AST.Nothing)  in
          let uu____7911 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____7911
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____7934 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____7934
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____8019 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____8019, (FStar_Pervasives_Native.snd post))  in
                    let uu____8030 =
                      let uu____8039 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____8039 then [] else [pre]  in
                    let uu____8074 =
                      let uu____8083 =
                        let uu____8092 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____8092 then [] else [pats]  in
                      FStar_List.append [post1] uu____8083  in
                    FStar_List.append uu____8030 uu____8074
                | uu____8151 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____8185  ->
                   match uu____8185 with
                   | (e,uu____8197) ->
                       let uu____8202 = resugar_term' env e  in
                       (uu____8202, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_8227 =
              match uu___5_8227 with
              | [] -> l
              | hd::tl ->
                  (match hd with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____8260 = resugar_term' env e  in
                         (uu____8260, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl
                   | uu____8265 -> aux l tl)
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
        let uu____8312 = b  in
        match uu____8312 with
        | (x,aq) ->
            let uu____8321 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____8321
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____8335 =
                       let uu____8336 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____8336  in
                     FStar_Parser_AST.mk_binder uu____8335 r
                       FStar_Parser_AST.Type_level imp
                 | uu____8337 ->
                     let uu____8338 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____8338
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____8343 =
                          let uu____8344 =
                            let uu____8349 = bv_as_unique_ident x  in
                            (uu____8349, e)  in
                          FStar_Parser_AST.Annotated uu____8344  in
                        FStar_Parser_AST.mk_binder uu____8343 r
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
              let uu____8369 = FStar_Syntax_Syntax.range_of_bv v  in
              FStar_Parser_AST.mk_pattern a uu____8369  in
            let used = FStar_Util.set_mem v body_bv  in
            let pat =
              let uu____8373 =
                if used
                then
                  let uu____8375 =
                    let uu____8382 = bv_as_unique_ident v  in
                    (uu____8382, aqual)  in
                  FStar_Parser_AST.PatVar uu____8375
                else FStar_Parser_AST.PatWild aqual  in
              mk uu____8373  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____8389;
                  FStar_Syntax_Syntax.vars = uu____8390;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____8400 = FStar_Options.print_bound_var_types ()  in
                if uu____8400
                then
                  let uu____8403 =
                    let uu____8404 =
                      let uu____8415 =
                        let uu____8422 = resugar_term' env typ  in
                        (uu____8422, FStar_Pervasives_Native.None)  in
                      (pat, uu____8415)  in
                    FStar_Parser_AST.PatAscribed uu____8404  in
                  mk uu____8403
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
          let uu____8443 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____8443
            (fun aqual  ->
               let uu____8455 =
                 let uu____8460 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun uu____8471  ->
                      FStar_Pervasives_Native.Some uu____8471) uu____8460
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____8455)

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
          (let uu____8533 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____8533) &&
            (let uu____8536 =
               FStar_List.existsML
                 (fun uu____8549  ->
                    match uu____8549 with
                    | (pattern,is_implicit) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____8571)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____8576 -> false
                          | uu____8578 -> true  in
                        is_implicit && might_be_used) args
                in
             Prims.op_Negation uu____8536)
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
            let uu____8646 = may_drop_implicits args  in
            if uu____8646 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____8671  ->
                 match uu____8671 with
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
              ((let uu____8726 =
                  let uu____8728 =
                    let uu____8730 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____8730  in
                  Prims.op_Negation uu____8728  in
                if uu____8726
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
              let uu____8774 = filter_pattern_imp args  in
              (match uu____8774 with
               | (hd,false )::(tl,false )::[] ->
                   let hd' = aux hd (FStar_Pervasives_Native.Some false)  in
                   let uu____8824 =
                     aux tl (FStar_Pervasives_Native.Some false)  in
                   (match uu____8824 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____8843 =
                       let uu____8849 =
                         let uu____8851 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____8851
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____8849)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____8843);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____8904  ->
                        match uu____8904 with
                        | (p2,is_implicit) ->
                            if is_implicit
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____8921 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____8921)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____8929;
                 FStar_Syntax_Syntax.fv_delta = uu____8930;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____8959 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____8959 FStar_List.rev  in
              let args1 =
                let uu____8975 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____8995  ->
                          match uu____8995 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____8975 FStar_List.rev  in
              let rec map2 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd::tl) -> []
                | (hd::tl,[]) ->
                    let uu____9073 = map2 tl []  in
                    (hd,
                      (mk
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____9073
                | (hd1::tl1,hd2::tl2) ->
                    let uu____9096 = map2 tl1 tl2  in (hd1, hd2) ::
                      uu____9096
                 in
              let args2 =
                let uu____9114 = map2 fields1 args1  in
                FStar_All.pipe_right uu____9114 FStar_List.rev  in
              mk (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v ->
              let uu____9158 =
                let uu____9169 =
                  FStar_Ident.text_of_id v.FStar_Syntax_Syntax.ppname  in
                string_to_op uu____9169  in
              (match uu____9158 with
               | FStar_Pervasives_Native.Some (op,uu____9172) ->
                   let uu____9189 =
                     let uu____9190 =
                       let uu____9191 =
                         let uu____9197 =
                           FStar_Ident.range_of_id
                             v.FStar_Syntax_Syntax.ppname
                            in
                         (op, uu____9197)  in
                       FStar_Ident.mk_ident uu____9191  in
                     FStar_Parser_AST.PatOp uu____9190  in
                   mk uu____9189
               | FStar_Pervasives_Native.None  ->
                   let uu____9207 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v uu____9207 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____9212 ->
              let uu____9213 =
                let uu____9214 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____9214  in
              mk uu____9213
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
          let uu____9254 =
            let uu____9257 =
              let uu____9258 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____9258  in
            FStar_Pervasives_Native.Some uu____9257  in
          FStar_Pervasives_Native.Some uu____9254

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
          let uu____9270 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____9270

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_9278  ->
    match uu___6_9278 with
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
    | FStar_Syntax_Syntax.Reflectable uu____9285 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____9286 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____9287 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____9292 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____9301 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____9310 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_9316  ->
    match uu___7_9316 with
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
            (tylid,uvs,bs,t,uu____9359,datacons) ->
            let uu____9369 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____9397,uu____9398,uu____9399,inductive_lid,uu____9401,uu____9402)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____9409 -> failwith "unexpected"))
               in
            (match uu____9369 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____9430 = FStar_Options.print_implicits ()  in
                   if uu____9430 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____9447 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_9454  ->
                             match uu___8_9454 with
                             | FStar_Syntax_Syntax.RecordType uu____9456 ->
                                 true
                             | uu____9466 -> false))
                      in
                   if uu____9447
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____9504,univs,term,uu____9507,num,uu____9509)
                           ->
                           let uu____9516 =
                             let uu____9517 =
                               FStar_Syntax_Subst.compress term  in
                             uu____9517.FStar_Syntax_Syntax.n  in
                           (match uu____9516 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____9527)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____9584  ->
                                          match uu____9584 with
                                          | (b,qual) ->
                                              let uu____9601 =
                                                bv_as_unique_ident b  in
                                              let uu____9602 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____9601, uu____9602)))
                                   in
                                FStar_List.append mfields fields
                            | uu____9607 -> failwith "unexpected")
                       | uu____9615 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     let uu____9640 =
                       let uu____9659 = FStar_Ident.ident_of_lid tylid  in
                       (uu____9659, bs2, FStar_Pervasives_Native.None,
                         fields)
                        in
                     FStar_Parser_AST.TyconRecord uu____9640
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs,term,uu____9730,num,uu____9732) ->
                            let c =
                              let uu____9749 = FStar_Ident.ident_of_lid l  in
                              let uu____9750 =
                                let uu____9753 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____9753  in
                              (uu____9749, uu____9750, false)  in
                            c :: constructors
                        | uu____9767 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      let uu____9812 =
                        let uu____9836 = FStar_Ident.ident_of_lid tylid  in
                        (uu____9836, bs2, FStar_Pervasives_Native.None,
                          constructors)
                         in
                      FStar_Parser_AST.TyconVariant uu____9812)
                    in
                 (other_datacons, tyc))
        | uu____9852 ->
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
        let uu____9878 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____9878;
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
        let uu____9908 = ts  in
        match uu____9908 with
        | (univs,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____9921 =
              let uu____9922 =
                let uu____9933 =
                  let uu____9936 =
                    let uu____9937 =
                      let uu____9950 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____9950)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____9937  in
                  [uu____9936]  in
                (false, false, uu____9933)  in
              FStar_Parser_AST.Tycon uu____9922  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____9921
  
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
              let uu____10015 = resugar_tscheme'' env name ts  in
              [uu____10015]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____10033 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____10035 =
             let uu____10038 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____10040 =
               let uu____10043 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____10045 =
                 let uu____10048 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____10050 =
                   let uu____10053 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____10055 =
                     let uu____10058 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____10060 =
                       let uu____10063 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____10063 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____10058 :: uu____10060  in
                   uu____10053 :: uu____10055  in
                 uu____10048 :: uu____10050  in
               uu____10043 :: uu____10045  in
             uu____10038 :: uu____10040  in
           uu____10033 :: uu____10035)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____10093 =
        match uu____10093 with
        | (ts,uu____10100) -> resugar_tscheme'' env name ts  in
      let uu____10101 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____10103 =
        let uu____10106 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____10108 =
          let uu____10111 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____10113 =
            let uu____10116 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____10118 =
              let uu____10121 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____10121]  in
            uu____10116 :: uu____10118  in
          uu____10111 :: uu____10113  in
        uu____10106 :: uu____10108  in
      uu____10101 :: uu____10103
  
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
            let uu____10182 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____10182 with
            | (bs,action_defn) ->
                let uu____10189 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____10189 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____10199 = FStar_Options.print_implicits ()  in
                       if uu____10199
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____10209 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____10209 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____10226 =
                           let uu____10237 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____10237,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____10226  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
                       let uu____10258 =
                         let uu____10259 =
                           let uu____10270 =
                             let uu____10273 =
                               let uu____10274 =
                                 let uu____10287 =
                                   FStar_Ident.ident_of_lid
                                     d.FStar_Syntax_Syntax.action_name
                                    in
                                 (uu____10287, action_params2,
                                   FStar_Pervasives_Native.None, t)
                                  in
                               FStar_Parser_AST.TyconAbbrev uu____10274  in
                             [uu____10273]  in
                           (false, false, uu____10270)  in
                         FStar_Parser_AST.Tycon uu____10259  in
                       mk_decl r q uu____10258
                     else
                       (let uu____10300 =
                          let uu____10301 =
                            let uu____10312 =
                              let uu____10315 =
                                let uu____10316 =
                                  let uu____10329 =
                                    FStar_Ident.ident_of_lid
                                      d.FStar_Syntax_Syntax.action_name
                                     in
                                  (uu____10329, action_params2,
                                    FStar_Pervasives_Native.None,
                                    action_defn1)
                                   in
                                FStar_Parser_AST.TyconAbbrev uu____10316  in
                              [uu____10315]  in
                            (false, false, uu____10312)  in
                          FStar_Parser_AST.Tycon uu____10301  in
                        mk_decl r q uu____10300))
             in
          let eff_name =
            FStar_Ident.ident_of_lid ed.FStar_Syntax_Syntax.mname  in
          let uu____10341 =
            let uu____10346 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____10346
             in
          match uu____10341 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____10364 = FStar_Options.print_implicits ()  in
                if uu____10364 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____10374 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____10374 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10424) ->
          let uu____10433 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____10456 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____10474 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____10482 -> false
                    | uu____10499 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____10433 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____10537 se1 =
                 match uu____10537 with
                 | (datacon_ses1,tycons) ->
                     let uu____10563 = resugar_typ env datacon_ses1 se1  in
                     (match uu____10563 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____10578 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____10578 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____10613 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____10613
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____10624,uu____10625,uu____10626,uu____10627,uu____10628)
                              ->
                              let uu____10635 =
                                let uu____10636 =
                                  let uu____10637 =
                                    let uu____10644 =
                                      FStar_Ident.ident_of_lid l  in
                                    (uu____10644,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Parser_AST.Exception uu____10637  in
                                decl'_to_decl se1 uu____10636  in
                              FStar_Pervasives_Native.Some uu____10635
                          | uu____10647 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____10651 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____10657 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____10671) ->
          let uu____10676 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_10684  ->
                    match uu___9_10684 with
                    | FStar_Syntax_Syntax.Projector (uu____10686,uu____10687)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____10689 -> true
                    | uu____10691 -> false))
             in
          if uu____10676
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
             | FStar_Parser_AST.Let (isrec,lets,uu____10726) ->
                 let uu____10755 =
                   let uu____10756 =
                     let uu____10757 =
                       let uu____10768 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____10768)  in
                     FStar_Parser_AST.TopLevelLet uu____10757  in
                   decl'_to_decl se uu____10756  in
                 FStar_Pervasives_Native.Some uu____10755
             | uu____10805 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____10810,fml) ->
          let uu____10812 =
            let uu____10813 =
              let uu____10814 =
                let uu____10819 = FStar_Ident.ident_of_lid lid  in
                let uu____10820 = resugar_term' env fml  in
                (uu____10819, uu____10820)  in
              FStar_Parser_AST.Assume uu____10814  in
            decl'_to_decl se uu____10813  in
          FStar_Pervasives_Native.Some uu____10812
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10822 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____10822
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____10831,t) ->
                let uu____10841 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____10841
            | uu____10842 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____10850,t) ->
                let uu____10860 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____10860
            | uu____10861 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____10885 -> failwith "Should not happen hopefully"  in
          let uu____10895 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____10895
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____10905 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____10905 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____10917 = FStar_Options.print_implicits ()  in
                 if uu____10917 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____10933 =
                 let uu____10934 =
                   let uu____10935 =
                     let uu____10946 =
                       let uu____10949 =
                         let uu____10950 =
                           let uu____10963 = FStar_Ident.ident_of_lid lid  in
                           let uu____10964 = resugar_comp' env c1  in
                           (uu____10963, bs3, FStar_Pervasives_Native.None,
                             uu____10964)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____10950  in
                       [uu____10949]  in
                     (false, false, uu____10946)  in
                   FStar_Parser_AST.Tycon uu____10935  in
                 decl'_to_decl se uu____10934  in
               FStar_Pervasives_Native.Some uu____10933)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____10976 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____10976
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____10980 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_10988  ->
                    match uu___10_10988 with
                    | FStar_Syntax_Syntax.Projector (uu____10990,uu____10991)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____10993 -> true
                    | uu____10995 -> false))
             in
          if uu____10980
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____11003 =
                 (let uu____11007 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____11007) || (FStar_List.isEmpty uvs)
                  in
               if uu____11003
               then resugar_term' env t
               else
                 (let uu____11012 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____11012 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____11021 = resugar_term' env t1  in
                      label universes uu____11021)
                in
             let uu____11022 =
               let uu____11023 =
                 let uu____11024 =
                   let uu____11029 = FStar_Ident.ident_of_lid lid  in
                   (uu____11029, t')  in
                 FStar_Parser_AST.Val uu____11024  in
               decl'_to_decl se uu____11023  in
             FStar_Pervasives_Native.Some uu____11022)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____11036 =
            let uu____11037 =
              let uu____11038 =
                let uu____11045 =
                  FStar_List.map (fun l  -> FStar_Ident.ident_of_lid l) ids
                   in
                let uu____11050 = resugar_term' env t  in
                (uu____11045, uu____11050)  in
              FStar_Parser_AST.Splice uu____11038  in
            decl'_to_decl se uu____11037  in
          FStar_Pervasives_Native.Some uu____11036
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____11053 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____11070 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n,p,(uu____11089,t),uu____11091) ->
          let uu____11100 =
            let uu____11101 =
              let uu____11102 =
                let uu____11111 = resugar_term' env t  in
                (m, n, p, uu____11111)  in
              FStar_Parser_AST.Polymonadic_bind uu____11102  in
            decl'_to_decl se uu____11101  in
          FStar_Pervasives_Native.Some uu____11100
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____11135 = noenv resugar_term'  in uu____11135 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____11153 = noenv resugar_sigelt'  in uu____11153 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____11171 = noenv resugar_comp'  in uu____11171 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____11194 = noenv resugar_pat'  in uu____11194 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____11228 = noenv resugar_binder'  in uu____11228 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____11253 = noenv resugar_tscheme'  in uu____11253 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____11281 = noenv resugar_eff_decl'  in uu____11281 r q ed
  