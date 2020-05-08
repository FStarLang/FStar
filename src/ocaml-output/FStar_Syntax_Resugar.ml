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
        (let uu____72 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname
            in
         FStar_Util.starts_with FStar_Ident.reserved_prefix uu____72) ||
          (FStar_Options.print_real_names ())
         in
      if uu____68
      then
        let uu____76 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname
           in
        let uu____78 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat uu____76 uu____78
      else FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname  in
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
               (FStar_Syntax_Syntax.Meta
               (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____165,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____166)) -> false
            | (uu____171,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____172)) -> false
            | uu____176 -> true))
  
let filter_pattern_imp :
  'uuuuuu189 .
    ('uuuuuu189 * Prims.bool) Prims.list ->
      ('uuuuuu189 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____224  ->
         match uu____224 with
         | (uu____231,is_implicit) -> Prims.op_Negation is_implicit) xs
  
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
      | uu____281 -> (n, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs  ->
    let uu____294 = FStar_Options.print_universes ()  in
    if uu____294
    then
      let uu____298 =
        FStar_List.map (fun x  -> FStar_Ident.string_of_id x) univs  in
      FStar_All.pipe_right uu____298 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____347 ->
          let uu____348 = universe_to_int Prims.int_zero u  in
          (match uu____348 with
           | (n,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____359 =
                      let uu____360 =
                        let uu____361 =
                          let uu____373 = FStar_Util.string_of_int n  in
                          (uu____373, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____361  in
                      FStar_Parser_AST.Const uu____360  in
                    mk uu____359 r
                | uu____386 ->
                    let e1 =
                      let uu____388 =
                        let uu____389 =
                          let uu____390 =
                            let uu____402 = FStar_Util.string_of_int n  in
                            (uu____402, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____390  in
                        FStar_Parser_AST.Const uu____389  in
                      mk uu____388 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____416 =
                      let uu____417 =
                        let uu____424 = FStar_Ident.id_of_text "+"  in
                        (uu____424, [e1; e2])  in
                      FStar_Parser_AST.Op uu____417  in
                    mk uu____416 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____432 ->
               let t =
                 let uu____436 =
                   let uu____437 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____437  in
                 mk uu____436 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____446 =
                        let uu____447 =
                          let uu____454 = resugar_universe x r  in
                          (acc, uu____454, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____447  in
                      mk uu____446 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____456 -> mk FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____470 =
              let uu____476 =
                let uu____478 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____478  in
              (uu____476, r)  in
            FStar_Ident.mk_ident uu____470  in
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
    let name_of_op uu___1_532 =
      match uu___1_532 with
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
      | uu____860 -> FStar_Pervasives_Native.None  in
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
    | uu____1000 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____1018 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____1018 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1036 ->
               let maybeop =
                 let uu____1044 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match acc with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op,uu____1110)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____1044
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
      let uu____1449 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1449 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1519 ->
          let length =
            let uu____1528 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____1528  in
          let str =
            if length = Prims.int_zero
            then
              FStar_Ident.string_of_lid
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            else
              (let uu____1538 =
                 FStar_Ident.string_of_lid
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_Util.substring_from uu____1538 (length + Prims.int_one))
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
                (let uu____1625 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1625
                 then
                   let uu____1638 =
                     let uu____1647 =
                       FStar_Ident.string_of_lid
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        in
                     (uu____1647, FStar_Pervasives_Native.None)  in
                   FStar_Pervasives_Native.Some uu____1638
                 else FStar_Pervasives_Native.None)
       in
    let uu____1672 =
      let uu____1673 = FStar_Syntax_Subst.compress t  in
      uu____1673.FStar_Syntax_Syntax.n  in
    match uu____1672 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length =
          let uu____1685 =
            FStar_Ident.nsstr
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_String.length uu____1685  in
        let s =
          if length = Prims.int_zero
          then
            FStar_Ident.string_of_lid
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          else
            (let uu____1695 =
               FStar_Ident.string_of_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.substring_from uu____1695 (length + Prims.int_one))
           in
        let uu____1698 = string_to_op s  in
        (match uu____1698 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1738 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1755 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1772 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1783 -> true
    | uu____1785 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let uu____1801 = FStar_Ident.string_of_lid lid  in
    match uu____1801 with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1808 ->
        let uu____1810 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1810
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1824 = may_shorten lid  in
      if uu____1824 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1979 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1979  in
      let uu____1982 =
        let uu____1983 = FStar_Syntax_Subst.compress t  in
        uu____1983.FStar_Syntax_Syntax.n  in
      match uu____1982 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1986 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____2003 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____2003
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____2006 =
              let uu____2007 = bv_as_unique_ident x  in [uu____2007]  in
            FStar_Ident.lid_of_ids uu____2006  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____2010 =
              let uu____2011 = bv_as_unique_ident x  in [uu____2011]  in
            FStar_Ident.lid_of_ids uu____2010  in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length =
            let uu____2015 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_String.length uu____2015  in
          let s =
            if length = Prims.int_zero
            then FStar_Ident.string_of_lid a
            else
              (let uu____2025 = FStar_Ident.string_of_lid a  in
               FStar_Util.substring_from uu____2025 (length + Prims.int_one))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____2034 =
              let uu____2035 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____2035  in
            mk uu____2034
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
               | uu____2059 -> failwith "wrong projector format")
            else
              (let uu____2066 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid  in
               if uu____2066
               then
                 let uu____2069 =
                   let uu____2070 =
                     let uu____2071 =
                       let uu____2077 = FStar_Ident.range_of_lid a  in
                       ("SMTPat", uu____2077)  in
                     FStar_Ident.mk_ident uu____2071  in
                   FStar_Parser_AST.Tvar uu____2070  in
                 mk uu____2069
               else
                 (let uu____2082 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid
                     in
                  if uu____2082
                  then
                    let uu____2085 =
                      let uu____2086 =
                        let uu____2087 =
                          let uu____2093 = FStar_Ident.range_of_lid a  in
                          ("SMTPatOr", uu____2093)  in
                        FStar_Ident.mk_ident uu____2087  in
                      FStar_Parser_AST.Tvar uu____2086  in
                    mk uu____2085
                  else
                    (let uu____2098 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____2102 =
                            let uu____2104 =
                              FStar_String.get s Prims.int_zero  in
                            FStar_Char.uppercase uu____2104  in
                          let uu____2107 = FStar_String.get s Prims.int_zero
                             in
                          uu____2102 <> uu____2107)
                        in
                     if uu____2098
                     then
                       let uu____2112 =
                         let uu____2113 = maybe_shorten_fv env fv  in
                         FStar_Parser_AST.Var uu____2113  in
                       mk uu____2112
                     else
                       (let uu____2116 =
                          let uu____2117 =
                            let uu____2128 = maybe_shorten_fv env fv  in
                            (uu____2128, [])  in
                          FStar_Parser_AST.Construct uu____2117  in
                        mk uu____2116))))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2146 = FStar_Options.print_universes ()  in
          if uu____2146
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
                   let uu____2177 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs
                      in
                   FStar_List.append args uu____2177  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd, args1)) r l
             | uu____2200 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2208 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2208
          then
            let uu____2211 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk uu____2211
          else mk (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2216 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2237 -> ("Type", true)  in
          (match uu____2216 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2249 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk uu____2249  in
               let uu____2250 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2250
               then
                 let uu____2253 =
                   let uu____2254 =
                     let uu____2261 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2261, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2254  in
                 mk uu____2253
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2266) ->
          let uu____2291 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2291 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2307 = FStar_Options.print_implicits ()  in
                 if uu____2307 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2345  ->
                         match uu____2345 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2385 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2385 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2395 = FStar_Options.print_implicits ()  in
                 if uu____2395 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2406 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2406 FStar_List.rev  in
               let rec aux body3 uu___2_2431 =
                 match uu___2_2431 with
                 | [] -> body3
                 | hd::tl ->
                     let body4 = mk (FStar_Parser_AST.Product ([hd], body3))
                        in
                     aux body4 tl
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2447 =
            let uu____2452 =
              let uu____2453 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2453]  in
            FStar_Syntax_Subst.open_term uu____2452 phi  in
          (match uu____2447 with
           | (x1,phi1) ->
               let b =
                 let uu____2475 =
                   let uu____2478 = FStar_List.hd x1  in
                   resugar_binder' env uu____2478 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2475  in
               let uu____2485 =
                 let uu____2486 =
                   let uu____2491 = resugar_term' env phi1  in
                   (b, uu____2491)  in
                 FStar_Parser_AST.Refine uu____2486  in
               mk uu____2485)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2493;
             FStar_Syntax_Syntax.vars = uu____2494;_},(e,uu____2496)::[])
          when
          (let uu____2537 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2537) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last uu___3_2586 =
            match uu___3_2586 with
            | hd::[] -> [hd]
            | hd::tl -> last tl
            | uu____2656 -> failwith "last of an empty list"  in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2742,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2743))::tl ->
                  drop_implicits tl
              | uu____2762 -> args2  in
            let uu____2771 = drop_implicits args1  in
            match uu____2771 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2803::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2833 -> [a1; a2]  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2933  ->
                   match uu____2933 with
                   | (e2,qual) ->
                       let uu____2950 = resugar_term' env e2  in
                       let uu____2951 = resugar_imp env qual  in
                       (uu____2950, uu____2951)) args1
               in
            let uu____2952 = resugar_term' env e1  in
            match uu____2952 with
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
                     fun uu____2989  ->
                       match uu____2989 with
                       | (x,qual) -> mk (FStar_Parser_AST.App (acc, x, qual)))
                  e2 args2
             in
          let args1 =
            let uu____3005 = FStar_Options.print_implicits ()  in
            if uu____3005 then args else filter_imp args  in
          let uu____3020 = resugar_term_as_op e  in
          (match uu____3020 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("calc_finish",uu____3033) ->
               let uu____3041 = resugar_calc env t  in
               (match uu____3041 with
                | FStar_Pervasives_Native.Some r -> r
                | uu____3045 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("tuple",uu____3048) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____3073  ->
                        match uu____3073 with
                        | (x,uu____3085) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix ->
                                 let uu____3094 =
                                   let uu____3095 =
                                     let uu____3096 =
                                       let uu____3103 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____3103, [prefix; x1])  in
                                     FStar_Parser_AST.Op uu____3096  in
                                   mk uu____3095  in
                                 FStar_Pervasives_Native.Some uu____3094))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____3107) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last args1  in
               let body =
                 match args2 with
                 | (b,uu____3133)::[] -> b
                 | uu____3150 -> failwith "wrong arguments to dtuple"  in
               let uu____3160 =
                 let uu____3161 = FStar_Syntax_Subst.compress body  in
                 uu____3161.FStar_Syntax_Syntax.n  in
               (match uu____3160 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3166) ->
                    let uu____3191 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3191 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3201 = FStar_Options.print_implicits ()
                              in
                           if uu____3201 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3218 =
                           let uu____3219 =
                             let uu____3230 =
                               FStar_List.map
                                 (fun uu____3241  ->
                                    FStar_Util.Inl uu____3241) xs3
                                in
                             (uu____3230, body3)  in
                           FStar_Parser_AST.Sum uu____3219  in
                         mk uu____3218)
                | uu____3248 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3271  ->
                              match uu____3271 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3289) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3298) when
               let uu____3306 =
                 FStar_Ident.string_of_lid FStar_Parser_Const.sread_lid  in
               ref_read = uu____3306 ->
               let uu____3309 = FStar_List.hd args1  in
               (match uu____3309 with
                | (t1,uu____3323) ->
                    let uu____3328 =
                      let uu____3329 = FStar_Syntax_Subst.compress t1  in
                      uu____3329.FStar_Syntax_Syntax.n  in
                    (match uu____3328 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         let uu____3333 =
                           FStar_Ident.string_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Util.field_projector_contains_constructor
                           uu____3333
                         ->
                         let f =
                           let uu____3336 =
                             let uu____3337 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             [uu____3337]  in
                           FStar_Ident.lid_of_path uu____3336
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3341 =
                           let uu____3342 =
                             let uu____3347 = resugar_term' env t1  in
                             (uu____3347, f)  in
                           FStar_Parser_AST.Project uu____3342  in
                         mk uu____3341
                     | uu____3348 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3349) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___435_3376  ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1  in
                         let uu____3386 =
                           match new_args with
                           | (a1,uu____3396)::(a2,uu____3398)::[] -> (a1, a2)
                           | uu____3425 ->
                               failwith "wrong arguments to try_with"
                            in
                         (match uu____3386 with
                          | (body,handler) ->
                              let decomp term =
                                let uu____3447 =
                                  let uu____3448 =
                                    FStar_Syntax_Subst.compress term  in
                                  uu____3448.FStar_Syntax_Syntax.n  in
                                match uu____3447 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x,e1,uu____3453) ->
                                    let uu____3478 =
                                      FStar_Syntax_Subst.open_term x e1  in
                                    (match uu____3478 with | (x1,e2) -> e2)
                                | uu____3485 ->
                                    let uu____3486 =
                                      let uu____3488 =
                                        let uu____3490 =
                                          resugar_term' env term  in
                                        FStar_Parser_AST.term_to_string
                                          uu____3490
                                         in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____3488
                                       in
                                    failwith uu____3486
                                 in
                              let body1 =
                                let uu____3493 = decomp body  in
                                resugar_term' env uu____3493  in
                              let handler1 =
                                let uu____3495 = decomp handler  in
                                resugar_term' env uu____3495  in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1,(uu____3503,uu____3504,b)::[]) -> b
                                | FStar_Parser_AST.Let
                                    (uu____3536,uu____3537,b) -> b
                                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                                    let uu____3574 =
                                      let uu____3575 =
                                        let uu____3584 = resugar_body t11  in
                                        (uu____3584, t2, t3)  in
                                      FStar_Parser_AST.Ascribed uu____3575
                                       in
                                    mk uu____3574
                                | uu____3587 ->
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
                                | uu____3645 -> []  in
                              let branches = resugar_branches handler1  in
                              mk (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3678 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with",uu____3679) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3688) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3711) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs',(uu____3776,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs',(uu____3808,pats'),body) ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3839 -> (xs, pats, t1)  in
               let resugar_forall_body body =
                 let uu____3852 =
                   let uu____3853 = FStar_Syntax_Subst.compress body  in
                   uu____3853.FStar_Syntax_Syntax.n  in
                 match uu____3852 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3858) ->
                     let uu____3883 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3883 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3893 = FStar_Options.print_implicits ()
                               in
                            if uu____3893 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3909 =
                            let uu____3918 =
                              let uu____3919 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3919.FStar_Syntax_Syntax.n  in
                            match uu____3918 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3937 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3954,pats) ->
                                      let uu____3988 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____4032  ->
                                                     match uu____4032 with
                                                     | (e2,uu____4040) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3988, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____4056 =
                                        mk
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____4056)
                                  | uu____4065 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3937 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____4097 ->
                                let uu____4098 = resugar_term' env body2  in
                                ([], uu____4098)
                             in
                          (match uu____3909 with
                           | (pats,body3) ->
                               let uu____4115 = uncurry xs3 pats body3  in
                               (match uu____4115 with
                                | (xs4,pats1,body4) ->
                                    if op = "forall"
                                    then
                                      let uu____4146 =
                                        let uu____4147 =
                                          let uu____4166 =
                                            let uu____4177 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4177, pats1)  in
                                          (xs4, uu____4166, body4)  in
                                        FStar_Parser_AST.QForall uu____4147
                                         in
                                      mk uu____4146
                                    else
                                      (let uu____4200 =
                                         let uu____4201 =
                                           let uu____4220 =
                                             let uu____4231 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4231, pats1)  in
                                           (xs4, uu____4220, body4)  in
                                         FStar_Parser_AST.QExists uu____4201
                                          in
                                       mk uu____4200))))
                 | uu____4252 ->
                     if op = "forall"
                     then
                       let uu____4256 =
                         let uu____4257 =
                           let uu____4276 = resugar_term' env body  in
                           ([], ([], []), uu____4276)  in
                         FStar_Parser_AST.QForall uu____4257  in
                       mk uu____4256
                     else
                       (let uu____4299 =
                          let uu____4300 =
                            let uu____4319 = resugar_term' env body  in
                            ([], ([], []), uu____4319)  in
                          FStar_Parser_AST.QExists uu____4300  in
                        mk uu____4299)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last args1  in
                 (match args2 with
                  | (b,uu____4358)::[] -> resugar_forall_body b
                  | uu____4375 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4387) ->
               let uu____4395 = FStar_List.hd args1  in
               (match uu____4395 with
                | (e1,uu____4409) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity1) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4481  ->
                         match uu____4481 with
                         | (e1,qual) ->
                             let uu____4498 = resugar_term' env e1  in
                             let uu____4499 = resugar_imp env qual  in
                             (uu____4498, uu____4499)))
                  in
               (match expected_arity1 with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4515 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4515 with
                       | (op_args,rest) ->
                           let head =
                             let uu____4563 =
                               let uu____4564 =
                                 let uu____4571 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4571)  in
                               FStar_Parser_AST.Op uu____4564  in
                             mk uu____4563  in
                           FStar_List.fold_left
                             (fun head1  ->
                                fun uu____4589  ->
                                  match uu____4589 with
                                  | (arg,qual) ->
                                      mk
                                        (FStar_Parser_AST.App
                                           (head1, arg, qual))) head rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n when
                    (FStar_List.length args1) = n ->
                    let uu____4608 =
                      let uu____4609 =
                        let uu____4616 =
                          let uu____4619 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4619
                           in
                        (op1, uu____4616)  in
                      FStar_Parser_AST.Op uu____4609  in
                    mk uu____4608
                | uu____4632 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4701 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4701 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4747 =
                   let uu____4760 =
                     let uu____4765 = resugar_pat' env pat1 branch_bv  in
                     let uu____4766 = resugar_term' env e  in
                     (uu____4765, uu____4766)  in
                   (FStar_Pervasives_Native.None, uu____4760)  in
                 [uu____4747]  in
               let body = resugar_term' env t2  in
               mk
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4818,t1)::(pat2,uu____4821,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4917 =
            let uu____4918 =
              let uu____4925 = resugar_term' env e  in
              let uu____4926 = resugar_term' env t1  in
              let uu____4927 = resugar_term' env t2  in
              (uu____4925, uu____4926, uu____4927)  in
            FStar_Parser_AST.If uu____4918  in
          mk uu____4917
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4993 =
            match uu____4993 with
            | (pat,wopt,b) ->
                let uu____5035 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____5035 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____5087 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____5087
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____5091 =
            let uu____5092 =
              let uu____5107 = resugar_term' env e  in
              let uu____5108 = FStar_List.map resugar_branch branches  in
              (uu____5107, uu____5108)  in
            FStar_Parser_AST.Match uu____5092  in
          mk uu____5091
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5154) ->
          let term =
            match asc with
            | FStar_Util.Inl n -> resugar_term' env n
            | FStar_Util.Inr n -> resugar_comp' env n  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5223 =
            let uu____5224 =
              let uu____5233 = resugar_term' env e  in
              (uu____5233, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5224  in
          mk uu____5223
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5262 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5262 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5316 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5316
                    in
                 let uu____5323 =
                   let uu____5328 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5328
                    in
                 match uu____5323 with
                 | (univs,td) ->
                     let uu____5348 =
                       let uu____5355 =
                         let uu____5356 = FStar_Syntax_Subst.compress td  in
                         uu____5356.FStar_Syntax_Syntax.n  in
                       match uu____5355 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5365,(t1,uu____5367)::(d,uu____5369)::[])
                           -> (t1, d)
                       | uu____5426 -> failwith "wrong let binding format"
                        in
                     (match uu____5348 with
                      | (typ,def) ->
                          let uu____5457 =
                            let uu____5473 =
                              let uu____5474 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5474.FStar_Syntax_Syntax.n  in
                            match uu____5473 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5494) ->
                                let uu____5519 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5519 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5550 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5550
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5573 -> ([], def, false)  in
                          (match uu____5457 with
                           | (binders,term,is_pat_app) ->
                               let uu____5628 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5639 =
                                       let uu____5640 =
                                         let uu____5641 =
                                           let uu____5648 =
                                             bv_as_unique_ident bv  in
                                           (uu____5648,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5641
                                          in
                                       mk_pat uu____5640  in
                                     (uu____5639, term)
                                  in
                               (match uu____5628 with
                                | (pat,term1) ->
                                    let uu____5670 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5713  ->
                                                  match uu____5713 with
                                                  | (bv,q) ->
                                                      let uu____5728 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5728
                                                        (fun q1  ->
                                                           let uu____5740 =
                                                             let uu____5741 =
                                                               let uu____5748
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5748,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5741
                                                              in
                                                           mk_pat uu____5740)))
                                           in
                                        let uu____5751 =
                                          let uu____5756 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5756)
                                           in
                                        let uu____5759 =
                                          universe_to_string univs  in
                                        (uu____5751, uu____5759)
                                      else
                                        (let uu____5768 =
                                           let uu____5773 =
                                             resugar_term' env term1  in
                                           (pat, uu____5773)  in
                                         let uu____5774 =
                                           universe_to_string univs  in
                                         (uu____5768, uu____5774))
                                       in
                                    (attrs_opt, uu____5670))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5880 =
                   match uu____5880 with
                   | (attrs,(pb,univs)) ->
                       let uu____5940 =
                         let uu____5942 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5942  in
                       if uu____5940
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____6023) ->
          let s =
            let uu____6042 =
              let uu____6044 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____6044 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____6042  in
          let uu____6049 = mk FStar_Parser_AST.Wild  in label s uu____6049
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____6057 =
            let uu____6058 =
              let uu____6063 = resugar_term' env tm  in (uu____6063, qi1)  in
            FStar_Parser_AST.Quote uu____6058  in
          mk uu____6057
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___4_6075 =
            match uu___4_6075 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____6083,(uu____6084,(p,t11))::[],t2) ->
                      mk (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6145 =
                        let uu____6146 =
                          let uu____6155 = resugar_seq t11  in
                          (uu____6155, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6146  in
                      mk uu____6145
                  | uu____6158 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6159,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6223  ->
                         match uu____6223 with
                         | (x,uu____6231) -> resugar_term' env x))
                  in
               mk (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6236 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____6247,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____6253,uu____6254,t1)
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
        let uu____6288 = FStar_Syntax_Util.head_and_args t  in
        match uu____6288 with
        | (hd,args) ->
            let uu____6337 =
              let uu____6352 =
                let uu____6353 =
                  let uu____6356 = FStar_Syntax_Util.un_uinst hd  in
                  FStar_Syntax_Subst.compress uu____6356  in
                uu____6353.FStar_Syntax_Syntax.n  in
              (uu____6352, args)  in
            (match uu____6337 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6374,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____6375))::(rel,FStar_Pervasives_Native.None
                                                                 )::(uu____6377,FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____6378))::
                (uu____6379,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6380))::(pf,FStar_Pervasives_Native.None
                                                              )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_finish_lid
                 ->
                 let pf1 = FStar_Syntax_Util.unthunk pf  in
                 FStar_Pervasives_Native.Some (rel, pf1)
             | uu____6478 -> FStar_Pervasives_Native.None)
         in
      let un_eta_rel rel =
        let bv_eq_tm b t =
          let uu____6520 =
            let uu____6521 = FStar_Syntax_Subst.compress t  in
            uu____6521.FStar_Syntax_Syntax.n  in
          match uu____6520 with
          | FStar_Syntax_Syntax.Tm_name b' when
              FStar_Syntax_Syntax.bv_eq b b' -> true
          | uu____6527 -> false  in
        let uu____6529 =
          let uu____6530 = FStar_Syntax_Subst.compress rel  in
          uu____6530.FStar_Syntax_Syntax.n  in
        match uu____6529 with
        | FStar_Syntax_Syntax.Tm_abs (b1::b2::[],body,uu____6538) ->
            let uu____6585 = FStar_Syntax_Subst.open_term [b1; b2] body  in
            (match uu____6585 with
             | (b11::b21::[],body1) ->
                 let body2 = FStar_Syntax_Util.unascribe body1  in
                 let body3 =
                   let uu____6645 = FStar_Syntax_Util.unb2t body2  in
                   match uu____6645 with
                   | FStar_Pervasives_Native.Some body3 -> body3
                   | FStar_Pervasives_Native.None  -> body2  in
                 let uu____6649 =
                   let uu____6650 = FStar_Syntax_Subst.compress body3  in
                   uu____6650.FStar_Syntax_Syntax.n  in
                 (match uu____6649 with
                  | FStar_Syntax_Syntax.Tm_app (e,args) when
                      (FStar_List.length args) >= (Prims.of_int (2)) ->
                      (match FStar_List.rev args with
                       | (a1,FStar_Pervasives_Native.None )::(a2,FStar_Pervasives_Native.None
                                                              )::rest
                           ->
                           let uu____6741 =
                             (bv_eq_tm (FStar_Pervasives_Native.fst b11) a2)
                               &&
                               (bv_eq_tm (FStar_Pervasives_Native.fst b21) a1)
                              in
                           if uu____6741
                           then
                             let uu____6750 =
                               FStar_Syntax_Util.mk_app e
                                 (FStar_List.rev rest)
                                in
                             FStar_All.pipe_left
                               (fun uu____6761  ->
                                  FStar_Pervasives_Native.Some uu____6761)
                               uu____6750
                           else FStar_Pervasives_Native.Some rel
                       | uu____6764 -> FStar_Pervasives_Native.Some rel)
                  | uu____6775 -> FStar_Pervasives_Native.Some rel))
        | uu____6776 -> FStar_Pervasives_Native.Some rel  in
      let resugar_step pack =
        let uu____6803 = FStar_Syntax_Util.head_and_args pack  in
        match uu____6803 with
        | (hd,args) ->
            let uu____6856 =
              let uu____6871 =
                let uu____6872 =
                  let uu____6875 = FStar_Syntax_Util.un_uinst hd  in
                  FStar_Syntax_Subst.compress uu____6875  in
                uu____6872.FStar_Syntax_Syntax.n  in
              (uu____6871, args)  in
            (match uu____6856 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6897,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____6898))::(uu____6899,FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Syntax.Implicit
                                                                 uu____6900))::
                (uu____6901,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6902))::(rel,FStar_Pervasives_Native.None
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
             | uu____7036 -> FStar_Pervasives_Native.None)
         in
      let resugar_init pack =
        let uu____7069 = FStar_Syntax_Util.head_and_args pack  in
        match uu____7069 with
        | (hd,args) ->
            let uu____7114 =
              let uu____7129 =
                let uu____7130 =
                  let uu____7133 = FStar_Syntax_Util.un_uinst hd  in
                  FStar_Syntax_Subst.compress uu____7133  in
                uu____7130.FStar_Syntax_Syntax.n  in
              (uu____7129, args)  in
            (match uu____7114 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____7147,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____7148))::(x,FStar_Pervasives_Native.None
                                                                 )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_init_lid
                 -> FStar_Pervasives_Native.Some x
             | uu____7197 -> FStar_Pervasives_Native.None)
         in
      let rec resugar_all_steps pack =
        let uu____7246 = resugar_step pack  in
        match uu____7246 with
        | FStar_Pervasives_Native.Some (t,r,j,k) ->
            let uu____7283 = resugar_all_steps k  in
            FStar_Util.bind_opt uu____7283
              (fun uu____7325  ->
                 match uu____7325 with
                 | (steps,k1) ->
                     FStar_Pervasives_Native.Some (((t, r, j) :: steps), k1))
        | FStar_Pervasives_Native.None  ->
            FStar_Pervasives_Native.Some ([], pack)
         in
      let resugar_rel rel =
        let rel1 =
          let uu____7437 = un_eta_rel rel  in
          match uu____7437 with
          | FStar_Pervasives_Native.Some rel1 -> rel1
          | FStar_Pervasives_Native.None  -> rel  in
        let fallback uu____7446 =
          let uu____7447 =
            let uu____7448 = resugar_term' env rel1  in
            FStar_Parser_AST.Paren uu____7448  in
          mk uu____7447  in
        let uu____7449 = FStar_Syntax_Util.head_and_args rel1  in
        match uu____7449 with
        | (hd,args) ->
            let uu____7492 =
              (FStar_Options.print_implicits ()) &&
                (FStar_List.existsb
                   (fun uu____7503  ->
                      match uu____7503 with
                      | (uu____7511,q) -> FStar_Syntax_Syntax.is_implicit q)
                   args)
               in
            if uu____7492
            then fallback ()
            else
              (let uu____7520 = resugar_term_as_op hd  in
               match uu____7520 with
               | FStar_Pervasives_Native.Some
                   (s,FStar_Pervasives_Native.None ) ->
                   let uu____7537 =
                     let uu____7538 =
                       let uu____7545 = FStar_Ident.id_of_text s  in
                       (uu____7545, [])  in
                     FStar_Parser_AST.Op uu____7538  in
                   mk uu____7537
               | FStar_Pervasives_Native.Some
                   (s,FStar_Pervasives_Native.Some uu____7557) when
                   uu____7557 = (Prims.of_int (2)) ->
                   let uu____7558 =
                     let uu____7559 =
                       let uu____7566 = FStar_Ident.id_of_text s  in
                       (uu____7566, [])  in
                     FStar_Parser_AST.Op uu____7559  in
                   mk uu____7558
               | uu____7569 -> fallback ())
         in
      let build_calc rel x0 steps =
        let r = resugar_term' env  in
        let uu____7614 =
          let uu____7615 =
            let uu____7624 = resugar_rel rel  in
            let uu____7625 = r x0  in
            let uu____7626 =
              FStar_List.map
                (fun uu____7640  ->
                   match uu____7640 with
                   | (z,rel1,j) ->
                       let uu____7650 =
                         let uu____7657 = resugar_rel rel1  in
                         let uu____7658 = r j  in
                         let uu____7659 = r z  in
                         (uu____7657, uu____7658, uu____7659)  in
                       FStar_Parser_AST.CalcStep uu____7650) steps
               in
            (uu____7624, uu____7625, uu____7626)  in
          FStar_Parser_AST.CalcProof uu____7615  in
        mk uu____7614  in
      let uu____7662 = resugar_calc_finish t0  in
      FStar_Util.bind_opt uu____7662
        (fun uu____7677  ->
           match uu____7677 with
           | (rel,pack) ->
               let uu____7686 = resugar_all_steps pack  in
               FStar_Util.bind_opt uu____7686
                 (fun uu____7717  ->
                    match uu____7717 with
                    | (steps,k) ->
                        let uu____7750 = resugar_init k  in
                        FStar_Util.bind_opt uu____7750
                          (fun x0  ->
                             let uu____7756 =
                               build_calc rel x0 (FStar_List.rev steps)  in
                             FStar_All.pipe_left
                               (fun uu____7765  ->
                                  FStar_Pervasives_Native.Some uu____7765)
                               uu____7756)))

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
               let uu____7800 = FStar_Options.print_universes ()  in
               if uu____7800
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
               let uu____7864 = FStar_Options.print_universes ()  in
               if uu____7864
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
            let uu____7908 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____7908, FStar_Parser_AST.Nothing)  in
          let uu____7909 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____7909
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____7932 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____7932
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____8017 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____8017, (FStar_Pervasives_Native.snd post))  in
                    let uu____8028 =
                      let uu____8037 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____8037 then [] else [pre]  in
                    let uu____8072 =
                      let uu____8081 =
                        let uu____8090 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____8090 then [] else [pats]  in
                      FStar_List.append [post1] uu____8081  in
                    FStar_List.append uu____8028 uu____8072
                | uu____8149 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____8183  ->
                   match uu____8183 with
                   | (e,uu____8195) ->
                       let uu____8200 = resugar_term' env e  in
                       (uu____8200, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___5_8225 =
              match uu___5_8225 with
              | [] -> l
              | hd::tl ->
                  (match hd with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____8258 = resugar_term' env e  in
                         (uu____8258, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl
                   | uu____8263 -> aux l tl)
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
        let uu____8310 = b  in
        match uu____8310 with
        | (x,aq) ->
            let uu____8319 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____8319
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____8333 =
                       let uu____8334 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____8334  in
                     FStar_Parser_AST.mk_binder uu____8333 r
                       FStar_Parser_AST.Type_level imp
                 | uu____8335 ->
                     let uu____8336 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____8336
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____8341 =
                          let uu____8342 =
                            let uu____8347 = bv_as_unique_ident x  in
                            (uu____8347, e)  in
                          FStar_Parser_AST.Annotated uu____8342  in
                        FStar_Parser_AST.mk_binder uu____8341 r
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
              let uu____8367 = FStar_Syntax_Syntax.range_of_bv v  in
              FStar_Parser_AST.mk_pattern a uu____8367  in
            let used = FStar_Util.set_mem v body_bv  in
            let pat =
              let uu____8371 =
                if used
                then
                  let uu____8373 =
                    let uu____8380 = bv_as_unique_ident v  in
                    (uu____8380, aqual)  in
                  FStar_Parser_AST.PatVar uu____8373
                else FStar_Parser_AST.PatWild aqual  in
              mk uu____8371  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____8387;
                  FStar_Syntax_Syntax.vars = uu____8388;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____8398 = FStar_Options.print_bound_var_types ()  in
                if uu____8398
                then
                  let uu____8401 =
                    let uu____8402 =
                      let uu____8413 =
                        let uu____8420 = resugar_term' env typ  in
                        (uu____8420, FStar_Pervasives_Native.None)  in
                      (pat, uu____8413)  in
                    FStar_Parser_AST.PatAscribed uu____8402  in
                  mk uu____8401
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
          let uu____8441 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____8441
            (fun aqual  ->
               let uu____8453 =
                 let uu____8458 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun uu____8469  ->
                      FStar_Pervasives_Native.Some uu____8469) uu____8458
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____8453)

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
          (let uu____8531 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____8531) &&
            (let uu____8534 =
               FStar_List.existsML
                 (fun uu____8547  ->
                    match uu____8547 with
                    | (pattern,is_implicit) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____8569)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____8574 -> false
                          | uu____8576 -> true  in
                        is_implicit && might_be_used) args
                in
             Prims.op_Negation uu____8534)
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
            let uu____8644 = may_drop_implicits args  in
            if uu____8644 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____8669  ->
                 match uu____8669 with
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
              ((let uu____8724 =
                  let uu____8726 =
                    let uu____8728 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____8728  in
                  Prims.op_Negation uu____8726  in
                if uu____8724
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
              let uu____8772 = filter_pattern_imp args  in
              (match uu____8772 with
               | (hd,false )::(tl,false )::[] ->
                   let hd' = aux hd (FStar_Pervasives_Native.Some false)  in
                   let uu____8822 =
                     aux tl (FStar_Pervasives_Native.Some false)  in
                   (match uu____8822 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____8841 =
                       let uu____8847 =
                         let uu____8849 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____8849
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____8847)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____8841);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____8902  ->
                        match uu____8902 with
                        | (p2,is_implicit) ->
                            if is_implicit
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____8919 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____8919)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____8927;
                 FStar_Syntax_Syntax.fv_delta = uu____8928;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____8957 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____8957 FStar_List.rev  in
              let args1 =
                let uu____8973 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____8993  ->
                          match uu____8993 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____8973 FStar_List.rev  in
              let rec map2 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd::tl) -> []
                | (hd::tl,[]) ->
                    let uu____9071 = map2 tl []  in
                    (hd,
                      (mk
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____9071
                | (hd1::tl1,hd2::tl2) ->
                    let uu____9094 = map2 tl1 tl2  in (hd1, hd2) ::
                      uu____9094
                 in
              let args2 =
                let uu____9112 = map2 fields1 args1  in
                FStar_All.pipe_right uu____9112 FStar_List.rev  in
              mk (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v ->
              let uu____9156 =
                let uu____9167 =
                  FStar_Ident.string_of_id v.FStar_Syntax_Syntax.ppname  in
                string_to_op uu____9167  in
              (match uu____9156 with
               | FStar_Pervasives_Native.Some (op,uu____9170) ->
                   let uu____9187 =
                     let uu____9188 =
                       let uu____9189 =
                         let uu____9195 =
                           FStar_Ident.range_of_id
                             v.FStar_Syntax_Syntax.ppname
                            in
                         (op, uu____9195)  in
                       FStar_Ident.mk_ident uu____9189  in
                     FStar_Parser_AST.PatOp uu____9188  in
                   mk uu____9187
               | FStar_Pervasives_Native.None  ->
                   let uu____9205 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v uu____9205 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____9210 ->
              let uu____9211 =
                let uu____9212 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____9212  in
              mk uu____9211
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
          let uu____9252 =
            let uu____9255 =
              let uu____9256 =
                let uu____9257 = resugar_term' env t  in
                FStar_Parser_AST.Arg_qualifier_meta_tac uu____9257  in
              FStar_Parser_AST.Meta uu____9256  in
            FStar_Pervasives_Native.Some uu____9255  in
          FStar_Pervasives_Native.Some uu____9252
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____9263 =
            let uu____9266 =
              let uu____9267 =
                let uu____9268 = resugar_term' env t  in
                FStar_Parser_AST.Arg_qualifier_meta_attr uu____9268  in
              FStar_Parser_AST.Meta uu____9267  in
            FStar_Pervasives_Native.Some uu____9266  in
          FStar_Pervasives_Native.Some uu____9263

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
          let uu____9280 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____9280
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          FStar_Parser_AST.Nothing

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_9291  ->
    match uu___6_9291 with
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
    | FStar_Syntax_Syntax.Reflectable uu____9298 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____9299 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____9300 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____9305 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____9314 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____9323 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_9329  ->
    match uu___7_9329 with
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
            (tylid,uvs,bs,t,uu____9372,datacons) ->
            let uu____9382 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____9410,uu____9411,uu____9412,inductive_lid,uu____9414,uu____9415)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____9422 -> failwith "unexpected"))
               in
            (match uu____9382 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____9443 = FStar_Options.print_implicits ()  in
                   if uu____9443 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____9460 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_9467  ->
                             match uu___8_9467 with
                             | FStar_Syntax_Syntax.RecordType uu____9469 ->
                                 true
                             | uu____9479 -> false))
                      in
                   if uu____9460
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____9517,univs,term,uu____9520,num,uu____9522)
                           ->
                           let uu____9529 =
                             let uu____9530 =
                               FStar_Syntax_Subst.compress term  in
                             uu____9530.FStar_Syntax_Syntax.n  in
                           (match uu____9529 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____9540)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____9597  ->
                                          match uu____9597 with
                                          | (b,qual) ->
                                              let uu____9614 =
                                                bv_as_unique_ident b  in
                                              let uu____9615 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____9614, uu____9615)))
                                   in
                                FStar_List.append mfields fields
                            | uu____9620 -> failwith "unexpected")
                       | uu____9628 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     let uu____9653 =
                       let uu____9672 = FStar_Ident.ident_of_lid tylid  in
                       (uu____9672, bs2, FStar_Pervasives_Native.None,
                         fields)
                        in
                     FStar_Parser_AST.TyconRecord uu____9653
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs,term,uu____9743,num,uu____9745) ->
                            let c =
                              let uu____9762 = FStar_Ident.ident_of_lid l  in
                              let uu____9763 =
                                let uu____9766 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____9766  in
                              (uu____9762, uu____9763, false)  in
                            c :: constructors
                        | uu____9780 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      let uu____9825 =
                        let uu____9849 = FStar_Ident.ident_of_lid tylid  in
                        (uu____9849, bs2, FStar_Pervasives_Native.None,
                          constructors)
                         in
                      FStar_Parser_AST.TyconVariant uu____9825)
                    in
                 (other_datacons, tyc))
        | uu____9865 ->
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
        let uu____9891 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____9891;
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
        let uu____9921 = ts  in
        match uu____9921 with
        | (univs,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____9934 =
              let uu____9935 =
                let uu____9946 =
                  let uu____9949 =
                    let uu____9950 =
                      let uu____9963 = resugar_term' env typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____9963)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____9950  in
                  [uu____9949]  in
                (false, false, uu____9946)  in
              FStar_Parser_AST.Tycon uu____9935  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____9934
  
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
              let uu____10028 = resugar_tscheme'' env name ts  in
              [uu____10028]
          | FStar_Pervasives_Native.None  -> []  in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr  in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr  in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr  in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____10046 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp
              in
           let uu____10048 =
             let uu____10051 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp
                in
             let uu____10053 =
               let uu____10056 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger
                  in
               let uu____10058 =
                 let uu____10061 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else
                    in
                 let uu____10063 =
                   let uu____10066 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp
                      in
                   let uu____10068 =
                     let uu____10071 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp
                        in
                     let uu____10073 =
                       let uu____10076 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial
                          in
                       uu____10076 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr))
                        in
                     uu____10071 :: uu____10073  in
                   uu____10066 :: uu____10068  in
                 uu____10061 :: uu____10063  in
               uu____10056 :: uu____10058  in
             uu____10051 :: uu____10053  in
           uu____10046 :: uu____10048)
  
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun combs  ->
      let resugar name uu____10106 =
        match uu____10106 with
        | (ts,uu____10113) -> resugar_tscheme'' env name ts  in
      let uu____10114 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr  in
      let uu____10116 =
        let uu____10119 = resugar "return" combs.FStar_Syntax_Syntax.l_return
           in
        let uu____10121 =
          let uu____10124 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind
             in
          let uu____10126 =
            let uu____10129 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp  in
            let uu____10131 =
              let uu____10134 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else
                 in
              [uu____10134]  in
            uu____10129 :: uu____10131  in
          uu____10124 :: uu____10126  in
        uu____10119 :: uu____10121  in
      uu____10114 :: uu____10116
  
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
            let uu____10195 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____10195 with
            | (bs,action_defn) ->
                let uu____10202 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____10202 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____10212 = FStar_Options.print_implicits ()  in
                       if uu____10212
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____10222 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b  -> resugar_binder' env b r))
                          in
                       FStar_All.pipe_right uu____10222 FStar_List.rev  in
                     let action_defn1 = resugar_term' env action_defn  in
                     let action_typ1 = resugar_term' env action_typ  in
                     if for_free
                     then
                       let a =
                         let uu____10239 =
                           let uu____10250 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____10250,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____10239  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
                       let uu____10271 =
                         let uu____10272 =
                           let uu____10283 =
                             let uu____10286 =
                               let uu____10287 =
                                 let uu____10300 =
                                   FStar_Ident.ident_of_lid
                                     d.FStar_Syntax_Syntax.action_name
                                    in
                                 (uu____10300, action_params2,
                                   FStar_Pervasives_Native.None, t)
                                  in
                               FStar_Parser_AST.TyconAbbrev uu____10287  in
                             [uu____10286]  in
                           (false, false, uu____10283)  in
                         FStar_Parser_AST.Tycon uu____10272  in
                       mk_decl r q uu____10271
                     else
                       (let uu____10313 =
                          let uu____10314 =
                            let uu____10325 =
                              let uu____10328 =
                                let uu____10329 =
                                  let uu____10342 =
                                    FStar_Ident.ident_of_lid
                                      d.FStar_Syntax_Syntax.action_name
                                     in
                                  (uu____10342, action_params2,
                                    FStar_Pervasives_Native.None,
                                    action_defn1)
                                   in
                                FStar_Parser_AST.TyconAbbrev uu____10329  in
                              [uu____10328]  in
                            (false, false, uu____10325)  in
                          FStar_Parser_AST.Tycon uu____10314  in
                        mk_decl r q uu____10313))
             in
          let eff_name =
            FStar_Ident.ident_of_lid ed.FStar_Syntax_Syntax.mname  in
          let uu____10354 =
            let uu____10359 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd
               in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____10359
             in
          match uu____10354 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____10377 = FStar_Options.print_implicits ()  in
                if uu____10377 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____10387 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b  -> resugar_binder' env b r))
                   in
                FStar_All.pipe_right uu____10387 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10437) ->
          let uu____10446 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____10469 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____10487 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____10495 -> false
                    | uu____10512 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____10446 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____10550 se1 =
                 match uu____10550 with
                 | (datacon_ses1,tycons) ->
                     let uu____10576 = resugar_typ env datacon_ses1 se1  in
                     (match uu____10576 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____10591 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____10591 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____10626 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons))
                            in
                         FStar_Pervasives_Native.Some uu____10626
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____10637,uu____10638,uu____10639,uu____10640,uu____10641)
                              ->
                              let uu____10648 =
                                let uu____10649 =
                                  let uu____10650 =
                                    let uu____10657 =
                                      FStar_Ident.ident_of_lid l  in
                                    (uu____10657,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Parser_AST.Exception uu____10650  in
                                decl'_to_decl se1 uu____10649  in
                              FStar_Pervasives_Native.Some uu____10648
                          | uu____10660 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____10664 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____10670 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____10684) ->
          let uu____10689 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_10697  ->
                    match uu___9_10697 with
                    | FStar_Syntax_Syntax.Projector (uu____10699,uu____10700)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____10702 -> true
                    | uu____10704 -> false))
             in
          if uu____10689
          then FStar_Pervasives_Native.None
          else
            (let mk e =
               FStar_Syntax_Syntax.mk e se.FStar_Syntax_Syntax.sigrng  in
             let dummy = mk FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let = mk (FStar_Syntax_Syntax.Tm_let (lbs, dummy))
                in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____10739) ->
                 let uu____10768 =
                   let uu____10769 =
                     let uu____10770 =
                       let uu____10781 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____10781)  in
                     FStar_Parser_AST.TopLevelLet uu____10770  in
                   decl'_to_decl se uu____10769  in
                 FStar_Pervasives_Native.Some uu____10768
             | uu____10818 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____10823,fml) ->
          let uu____10825 =
            let uu____10826 =
              let uu____10827 =
                let uu____10832 = FStar_Ident.ident_of_lid lid  in
                let uu____10833 = resugar_term' env fml  in
                (uu____10832, uu____10833)  in
              FStar_Parser_AST.Assume uu____10827  in
            decl'_to_decl se uu____10826  in
          FStar_Pervasives_Native.Some uu____10825
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10835 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____10835
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____10844,t) ->
                let uu____10854 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____10854
            | uu____10855 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____10863,t) ->
                let uu____10873 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____10873
            | uu____10874 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____10898 -> failwith "Should not happen hopefully"  in
          let uu____10908 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____10908
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____10918 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____10918 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____10930 = FStar_Options.print_implicits ()  in
                 if uu____10930 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____10946 =
                 let uu____10947 =
                   let uu____10948 =
                     let uu____10959 =
                       let uu____10962 =
                         let uu____10963 =
                           let uu____10976 = FStar_Ident.ident_of_lid lid  in
                           let uu____10977 = resugar_comp' env c1  in
                           (uu____10976, bs3, FStar_Pervasives_Native.None,
                             uu____10977)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____10963  in
                       [uu____10962]  in
                     (false, false, uu____10959)  in
                   FStar_Parser_AST.Tycon uu____10948  in
                 decl'_to_decl se uu____10947  in
               FStar_Pervasives_Native.Some uu____10946)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____10989 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____10989
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____10993 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_11001  ->
                    match uu___10_11001 with
                    | FStar_Syntax_Syntax.Projector (uu____11003,uu____11004)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____11006 -> true
                    | uu____11008 -> false))
             in
          if uu____10993
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____11016 =
                 (let uu____11020 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____11020) || (FStar_List.isEmpty uvs)
                  in
               if uu____11016
               then resugar_term' env t
               else
                 (let uu____11025 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____11025 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____11034 = resugar_term' env t1  in
                      label universes uu____11034)
                in
             let uu____11035 =
               let uu____11036 =
                 let uu____11037 =
                   let uu____11042 = FStar_Ident.ident_of_lid lid  in
                   (uu____11042, t')  in
                 FStar_Parser_AST.Val uu____11037  in
               decl'_to_decl se uu____11036  in
             FStar_Pervasives_Native.Some uu____11035)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____11049 =
            let uu____11050 =
              let uu____11051 =
                let uu____11058 =
                  FStar_List.map (fun l  -> FStar_Ident.ident_of_lid l) ids
                   in
                let uu____11063 = resugar_term' env t  in
                (uu____11058, uu____11063)  in
              FStar_Parser_AST.Splice uu____11051  in
            decl'_to_decl se uu____11050  in
          FStar_Pervasives_Native.Some uu____11049
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____11066 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____11083 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m,n,p,(uu____11102,t),uu____11104) ->
          let uu____11113 =
            let uu____11114 =
              let uu____11115 =
                let uu____11124 = resugar_term' env t  in
                (m, n, p, uu____11124)  in
              FStar_Parser_AST.Polymonadic_bind uu____11115  in
            decl'_to_decl se uu____11114  in
          FStar_Pervasives_Native.Some uu____11113
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____11148 = noenv resugar_term'  in uu____11148 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____11166 = noenv resugar_sigelt'  in uu____11166 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____11184 = noenv resugar_comp'  in uu____11184 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____11207 = noenv resugar_pat'  in uu____11207 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____11241 = noenv resugar_binder'  in uu____11241 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____11266 = noenv resugar_tscheme'  in uu____11266 ts 
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun ed  ->
        let uu____11294 = noenv resugar_eff_decl'  in uu____11294 r q ed
  