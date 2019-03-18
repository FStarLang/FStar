open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____51292 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____51292
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____51300 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____51300
  
let map_opt :
  'Auu____51310 'Auu____51311 .
    unit ->
      ('Auu____51310 -> 'Auu____51311 FStar_Pervasives_Native.option) ->
        'Auu____51310 Prims.list -> 'Auu____51311 Prims.list
  = fun uu____51327  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____51336 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____51336
      then
        let uu____51340 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____51340
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____51350 .
    ('Auu____51350 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51350 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_51405  ->
            match uu___429_51405 with
            | (uu____51413,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____51420,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____51421)) -> false
            | (uu____51426,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____51427)) -> false
            | uu____51433 -> true))
  
let filter_pattern_imp :
  'Auu____51446 .
    ('Auu____51446 * Prims.bool) Prims.list ->
      ('Auu____51446 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____51481  ->
         match uu____51481 with
         | (uu____51488,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____51538 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____51551 = FStar_Options.print_universes ()  in
    if uu____51551
    then
      let uu____51555 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____51555 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____51619 ->
          let uu____51620 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____51620 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____51631 =
                      let uu____51632 =
                        let uu____51633 =
                          let uu____51645 = FStar_Util.string_of_int n1  in
                          (uu____51645, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____51633  in
                      FStar_Parser_AST.Const uu____51632  in
                    mk1 uu____51631 r
                | uu____51658 ->
                    let e1 =
                      let uu____51660 =
                        let uu____51661 =
                          let uu____51662 =
                            let uu____51674 = FStar_Util.string_of_int n1  in
                            (uu____51674, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____51662  in
                        FStar_Parser_AST.Const uu____51661  in
                      mk1 uu____51660 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____51688 =
                      let uu____51689 =
                        let uu____51696 = FStar_Ident.id_of_text "+"  in
                        (uu____51696, [e1; e2])  in
                      FStar_Parser_AST.Op uu____51689  in
                    mk1 uu____51688 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____51704 ->
               let t =
                 let uu____51708 =
                   let uu____51709 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____51709  in
                 mk1 uu____51708 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____51718 =
                        let uu____51719 =
                          let uu____51726 = resugar_universe x r  in
                          (acc, uu____51726, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____51719  in
                      mk1 uu____51718 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____51728 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____51740 =
              let uu____51746 =
                let uu____51748 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____51748  in
              (uu____51746, r)  in
            FStar_Ident.mk_ident uu____51740  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_51786 =
      match uu___430_51786 with
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
      | uu____52114 -> FStar_Pervasives_Native.None  in
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
    | uu____52254 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____52272 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____52272 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____52290 ->
               let op =
                 let uu____52296 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____52350) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____52296
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
      let uu____52677 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____52677 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____52747 ->
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
                (let uu____52849 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____52849
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____52885 =
      let uu____52886 = FStar_Syntax_Subst.compress t  in
      uu____52886.FStar_Syntax_Syntax.n  in
    match uu____52885 with
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
        let uu____52907 = string_to_op s  in
        (match uu____52907 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____52947 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____52964 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____52981 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____52992 -> true
    | uu____52994 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____53015 ->
        let uu____53017 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____53017
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____53031 = may_shorten lid  in
      if uu____53031 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____53176 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____53176  in
      let uu____53179 =
        let uu____53180 = FStar_Syntax_Subst.compress t  in
        uu____53180.FStar_Syntax_Syntax.n  in
      match uu____53179 with
      | FStar_Syntax_Syntax.Tm_delayed uu____53183 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____53208 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____53208
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____53211 =
              let uu____53214 = bv_as_unique_ident x  in [uu____53214]  in
            FStar_Ident.lid_of_ids uu____53211  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____53217 =
              let uu____53220 = bv_as_unique_ident x  in [uu____53220]  in
            FStar_Ident.lid_of_ids uu____53217  in
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
            let uu____53239 =
              let uu____53240 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____53240  in
            mk1 uu____53239
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
               | uu____53264 -> failwith "wrong projector format")
            else
              (let uu____53271 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____53275 =
                      let uu____53277 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____53277  in
                    let uu____53280 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____53275 <> uu____53280)
                  in
               if uu____53271
               then
                 let uu____53285 =
                   let uu____53286 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____53286  in
                 mk1 uu____53285
               else
                 (let uu____53289 =
                    let uu____53290 =
                      let uu____53301 = maybe_shorten_fv env fv  in
                      (uu____53301, [])  in
                    FStar_Parser_AST.Construct uu____53290  in
                  mk1 uu____53289))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____53319 = FStar_Options.print_universes ()  in
          if uu____53319
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
                   let uu____53350 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____53350  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____53373 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____53381 = FStar_Syntax_Syntax.is_teff t  in
          if uu____53381
          then
            let uu____53384 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____53384
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____53389 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____53410 -> ("Type", true)  in
          (match uu____53389 with
           | (nm,needs_app) ->
               let typ =
                 let uu____53422 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____53422  in
               let uu____53423 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____53423
               then
                 let uu____53426 =
                   let uu____53427 =
                     let uu____53434 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____53434, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____53427  in
                 mk1 uu____53426
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____53439) ->
          let uu____53464 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____53464 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53480 = FStar_Options.print_implicits ()  in
                 if uu____53480 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____53518  ->
                         match uu____53518 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____53558 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____53558 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53568 = FStar_Options.print_implicits ()  in
                 if uu____53568 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____53579 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____53579 FStar_List.rev  in
               let rec aux body3 uu___431_53604 =
                 match uu___431_53604 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____53620 =
            let uu____53625 =
              let uu____53626 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____53626]  in
            FStar_Syntax_Subst.open_term uu____53625 phi  in
          (match uu____53620 with
           | (x1,phi1) ->
               let b =
                 let uu____53648 =
                   let uu____53651 = FStar_List.hd x1  in
                   resugar_binder' env uu____53651 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____53648  in
               let uu____53658 =
                 let uu____53659 =
                   let uu____53664 = resugar_term' env phi1  in
                   (b, uu____53664)  in
                 FStar_Parser_AST.Refine uu____53659  in
               mk1 uu____53658)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____53666;
             FStar_Syntax_Syntax.vars = uu____53667;_},(e,uu____53669)::[])
          when
          (let uu____53710 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____53710) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_53759 =
            match uu___432_53759 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____53829 -> failwith "last of an empty list"  in
          let rec last_two uu___433_53868 =
            match uu___433_53868 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____53900::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____53978::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____54049  ->
                   match uu____54049 with
                   | (e2,qual) ->
                       let uu____54066 = resugar_term' env e2  in
                       let uu____54067 = resugar_imp env qual  in
                       (uu____54066, uu____54067)) args1
               in
            let uu____54068 = resugar_term' env e1  in
            match uu____54068 with
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
                     fun uu____54105  ->
                       match uu____54105 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____54121 = FStar_Options.print_implicits ()  in
            if uu____54121 then args else filter_imp args  in
          let uu____54136 = resugar_term_as_op e  in
          (match uu____54136 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____54149) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____54174  ->
                        match uu____54174 with
                        | (x,uu____54186) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____54195 =
                                   let uu____54196 =
                                     let uu____54197 =
                                       let uu____54204 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____54204, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____54197  in
                                   mk1 uu____54196  in
                                 FStar_Pervasives_Native.Some uu____54195))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____54208) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____54234)::[] -> b
                 | uu____54251 -> failwith "wrong arguments to dtuple"  in
               let uu____54261 =
                 let uu____54262 = FStar_Syntax_Subst.compress body  in
                 uu____54262.FStar_Syntax_Syntax.n  in
               (match uu____54261 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54267) ->
                    let uu____54292 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____54292 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____54302 = FStar_Options.print_implicits ()
                              in
                           if uu____54302 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____54319 =
                           let uu____54320 =
                             let uu____54331 =
                               FStar_List.map
                                 (fun _54342  -> FStar_Util.Inl _54342) xs3
                                in
                             (uu____54331, body3)  in
                           FStar_Parser_AST.Sum uu____54320  in
                         mk1 uu____54319)
                | uu____54349 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____54372  ->
                              match uu____54372 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____54390) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____54399) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____54408 = FStar_List.hd args1  in
               (match uu____54408 with
                | (t1,uu____54422) ->
                    let uu____54427 =
                      let uu____54428 = FStar_Syntax_Subst.compress t1  in
                      uu____54428.FStar_Syntax_Syntax.n  in
                    (match uu____54427 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____54435 =
                           let uu____54436 =
                             let uu____54441 = resugar_term' env t1  in
                             (uu____54441, f)  in
                           FStar_Parser_AST.Project uu____54436  in
                         mk1 uu____54435
                     | uu____54442 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____54443) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____54467 =
                 match new_args with
                 | (a1,uu____54477)::(a2,uu____54479)::[] -> (a1, a2)
                 | uu____54506 -> failwith "wrong arguments to try_with"  in
               (match uu____54467 with
                | (body,handler) ->
                    let decomp term =
                      let uu____54528 =
                        let uu____54529 = FStar_Syntax_Subst.compress term
                           in
                        uu____54529.FStar_Syntax_Syntax.n  in
                      match uu____54528 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____54534) ->
                          let uu____54559 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____54559 with | (x1,e2) -> e2)
                      | uu____54566 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____54569 = decomp body  in
                      resugar_term' env uu____54569  in
                    let handler1 =
                      let uu____54571 = decomp handler  in
                      resugar_term' env uu____54571  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____54579,uu____54580,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____54612,uu____54613,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____54650 =
                            let uu____54651 =
                              let uu____54660 = resugar_body t11  in
                              (uu____54660, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____54651  in
                          mk1 uu____54650
                      | uu____54663 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____54721 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____54751) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54760) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54781) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____54879 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____54892 =
                   let uu____54893 = FStar_Syntax_Subst.compress body  in
                   uu____54893.FStar_Syntax_Syntax.n  in
                 match uu____54892 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54898) ->
                     let uu____54923 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____54923 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____54933 =
                              FStar_Options.print_implicits ()  in
                            if uu____54933 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____54949 =
                            let uu____54958 =
                              let uu____54959 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____54959.FStar_Syntax_Syntax.n  in
                            match uu____54958 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____54977 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____55007 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____55051  ->
                                                     match uu____55051 with
                                                     | (e2,uu____55059) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____55007, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____55075 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____55075)
                                  | uu____55084 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____54977 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____55116 ->
                                let uu____55117 = resugar_term' env body2  in
                                ([], uu____55117)
                             in
                          (match uu____54949 with
                           | (pats,body3) ->
                               let uu____55134 = uncurry xs3 pats body3  in
                               (match uu____55134 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      mk1
                                        (FStar_Parser_AST.QForall
                                           (xs5, pats1, body4))
                                    else
                                      mk1
                                        (FStar_Parser_AST.QExists
                                           (xs5, pats1, body4)))))
                 | uu____55186 ->
                     if op = "forall"
                     then
                       let uu____55190 =
                         let uu____55191 =
                           let uu____55204 = resugar_term' env body  in
                           ([], [[]], uu____55204)  in
                         FStar_Parser_AST.QForall uu____55191  in
                       mk1 uu____55190
                     else
                       (let uu____55217 =
                          let uu____55218 =
                            let uu____55231 = resugar_term' env body  in
                            ([], [[]], uu____55231)  in
                          FStar_Parser_AST.QExists uu____55218  in
                        mk1 uu____55217)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____55260)::[] -> resugar b
                  | uu____55277 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____55289) ->
               let uu____55297 = FStar_List.hd args1  in
               (match uu____55297 with
                | (e1,uu____55311) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____55383  ->
                         match uu____55383 with
                         | (e1,qual) ->
                             let uu____55400 = resugar_term' env e1  in
                             let uu____55401 = resugar_imp env qual  in
                             (uu____55400, uu____55401)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____55417 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____55417 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____55465 =
                               let uu____55466 =
                                 let uu____55473 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____55473)  in
                               FStar_Parser_AST.Op uu____55466  in
                             mk1 uu____55465  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____55491  ->
                                  match uu____55491 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____55510 =
                      let uu____55511 =
                        let uu____55518 =
                          let uu____55521 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____55521
                           in
                        (op1, uu____55518)  in
                      FStar_Parser_AST.Op uu____55511  in
                    mk1 uu____55510
                | uu____55534 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____55603 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____55603 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____55649 =
                   let uu____55662 =
                     let uu____55667 = resugar_pat' env pat1 branch_bv  in
                     let uu____55668 = resugar_term' env e  in
                     (uu____55667, uu____55668)  in
                   (FStar_Pervasives_Native.None, uu____55662)  in
                 [uu____55649]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____55720,t1)::(pat2,uu____55723,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____55819 =
            let uu____55820 =
              let uu____55827 = resugar_term' env e  in
              let uu____55828 = resugar_term' env t1  in
              let uu____55829 = resugar_term' env t2  in
              (uu____55827, uu____55828, uu____55829)  in
            FStar_Parser_AST.If uu____55820  in
          mk1 uu____55819
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____55895 =
            match uu____55895 with
            | (pat,wopt,b) ->
                let uu____55937 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____55937 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____55989 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____55989
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____55993 =
            let uu____55994 =
              let uu____56009 = resugar_term' env e  in
              let uu____56010 = FStar_List.map resugar_branch branches  in
              (uu____56009, uu____56010)  in
            FStar_Parser_AST.Match uu____55994  in
          mk1 uu____55993
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____56056) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____56125 =
            let uu____56126 =
              let uu____56135 = resugar_term' env e  in
              (uu____56135, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____56126  in
          mk1 uu____56125
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____56164 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____56164 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____56218 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____56218
                    in
                 let uu____56225 =
                   let uu____56230 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____56230
                    in
                 match uu____56225 with
                 | (univs1,td) ->
                     let uu____56250 =
                       let uu____56257 =
                         let uu____56258 = FStar_Syntax_Subst.compress td  in
                         uu____56258.FStar_Syntax_Syntax.n  in
                       match uu____56257 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____56267,(t1,uu____56269)::(d,uu____56271)::[])
                           -> (t1, d)
                       | uu____56328 -> failwith "wrong let binding format"
                        in
                     (match uu____56250 with
                      | (typ,def) ->
                          let uu____56359 =
                            let uu____56375 =
                              let uu____56376 =
                                FStar_Syntax_Subst.compress def  in
                              uu____56376.FStar_Syntax_Syntax.n  in
                            match uu____56375 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____56396)
                                ->
                                let uu____56421 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____56421 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____56452 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____56452
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____56475 -> ([], def, false)  in
                          (match uu____56359 with
                           | (binders,term,is_pat_app) ->
                               let uu____56530 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____56541 =
                                       let uu____56542 =
                                         let uu____56543 =
                                           let uu____56550 =
                                             bv_as_unique_ident bv  in
                                           (uu____56550,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____56543
                                          in
                                       mk_pat uu____56542  in
                                     (uu____56541, term)
                                  in
                               (match uu____56530 with
                                | (pat,term1) ->
                                    let uu____56572 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____56615  ->
                                                  match uu____56615 with
                                                  | (bv,q) ->
                                                      let uu____56630 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____56630
                                                        (fun q1  ->
                                                           let uu____56642 =
                                                             let uu____56643
                                                               =
                                                               let uu____56650
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____56650,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____56643
                                                              in
                                                           mk_pat uu____56642)))
                                           in
                                        let uu____56653 =
                                          let uu____56658 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____56658)
                                           in
                                        let uu____56661 =
                                          universe_to_string univs1  in
                                        (uu____56653, uu____56661)
                                      else
                                        (let uu____56670 =
                                           let uu____56675 =
                                             resugar_term' env term1  in
                                           (pat, uu____56675)  in
                                         let uu____56676 =
                                           universe_to_string univs1  in
                                         (uu____56670, uu____56676))
                                       in
                                    (attrs_opt, uu____56572))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____56782 =
                   match uu____56782 with
                   | (attrs,(pb,univs1)) ->
                       let uu____56842 =
                         let uu____56844 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____56844  in
                       if uu____56842
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____56925) ->
          let s =
            let uu____56944 =
              let uu____56946 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____56946 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____56944  in
          let uu____56951 = mk1 FStar_Parser_AST.Wild  in label s uu____56951
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____56959 =
            let uu____56960 =
              let uu____56965 = resugar_term' env tm  in (uu____56965, qi1)
               in
            FStar_Parser_AST.Quote uu____56960  in
          mk1 uu____56959
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_56977 =
            match uu___434_56977 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____56985,(uu____56986,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____57047 =
                        let uu____57048 =
                          let uu____57057 = resugar_seq t11  in
                          (uu____57057, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____57048  in
                      mk1 uu____57047
                  | uu____57060 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____57104  ->
                         match uu____57104 with
                         | (x,uu____57112) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____57117 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____57135,t1) ->
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
               let uu____57175 = FStar_Options.print_universes ()  in
               if uu____57175
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
               let uu____57239 = FStar_Options.print_universes ()  in
               if uu____57239
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
            let uu____57283 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____57283, FStar_Parser_AST.Nothing)  in
          let uu____57284 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____57284
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____57307 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____57307
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____57392 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____57392, (FStar_Pervasives_Native.snd post))  in
                    let uu____57403 =
                      let uu____57412 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____57412 then [] else [pre]  in
                    let uu____57447 =
                      let uu____57456 =
                        let uu____57465 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____57465 then [] else [pats]  in
                      FStar_List.append [post1] uu____57456  in
                    FStar_List.append uu____57403 uu____57447
                | uu____57524 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____57558  ->
                   match uu____57558 with
                   | (e,uu____57570) ->
                       let uu____57575 = resugar_term' env e  in
                       (uu____57575, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_57600 =
              match uu___435_57600 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____57633 = resugar_term' env e  in
                         (uu____57633, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____57638 -> aux l tl1)
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
        let uu____57685 = b  in
        match uu____57685 with
        | (x,aq) ->
            let uu____57694 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____57694
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____57708 =
                       let uu____57709 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____57709  in
                     FStar_Parser_AST.mk_binder uu____57708 r
                       FStar_Parser_AST.Type_level imp
                 | uu____57710 ->
                     let uu____57711 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____57711
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____57716 =
                          let uu____57717 =
                            let uu____57722 = bv_as_unique_ident x  in
                            (uu____57722, e)  in
                          FStar_Parser_AST.Annotated uu____57717  in
                        FStar_Parser_AST.mk_binder uu____57716 r
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
              let uu____57742 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____57742  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____57746 =
                if used
                then
                  let uu____57748 =
                    let uu____57755 = bv_as_unique_ident v1  in
                    (uu____57755, aqual)  in
                  FStar_Parser_AST.PatVar uu____57748
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____57746  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____57762;
                  FStar_Syntax_Syntax.vars = uu____57763;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____57773 = FStar_Options.print_bound_var_types ()  in
                if uu____57773
                then
                  let uu____57776 =
                    let uu____57777 =
                      let uu____57788 =
                        let uu____57795 = resugar_term' env typ  in
                        (uu____57795, FStar_Pervasives_Native.None)  in
                      (pat, uu____57788)  in
                    FStar_Parser_AST.PatAscribed uu____57777  in
                  mk1 uu____57776
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
          let uu____57816 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____57816
            (fun aqual  ->
               let uu____57828 =
                 let uu____57833 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _57844  -> FStar_Pervasives_Native.Some _57844)
                   uu____57833
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____57828)

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
          (let uu____57906 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____57906) &&
            (let uu____57909 =
               FStar_List.existsML
                 (fun uu____57922  ->
                    match uu____57922 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____57944)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____57949 -> false
                          | uu____57951 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____57909)
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
            let uu____58019 = may_drop_implicits args  in
            if uu____58019 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____58044  ->
                 match uu____58044 with
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
              ((let uu____58099 =
                  let uu____58101 =
                    let uu____58103 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____58103  in
                  Prims.op_Negation uu____58101  in
                if uu____58099
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
              let uu____58147 = filter_pattern_imp args  in
              (match uu____58147 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____58197 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____58197 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____58216 =
                       let uu____58222 =
                         let uu____58224 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____58224
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____58222)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____58216);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____58277  ->
                        match uu____58277 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____58294 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____58294)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____58302;
                 FStar_Syntax_Syntax.fv_delta = uu____58303;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____58332 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____58332 FStar_List.rev  in
              let args1 =
                let uu____58348 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____58368  ->
                          match uu____58368 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____58348 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____58446 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____58446
                | (hd1::tl1,hd2::tl2) ->
                    let uu____58469 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____58469
                 in
              let args2 =
                let uu____58487 = map21 fields1 args1  in
                FStar_All.pipe_right uu____58487 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____58531 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____58531 with
               | FStar_Pervasives_Native.Some (op,uu____58543) ->
                   let uu____58560 =
                     let uu____58561 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____58561  in
                   mk1 uu____58560
               | FStar_Pervasives_Native.None  ->
                   let uu____58571 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____58571 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____58576 ->
              let uu____58577 =
                let uu____58578 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____58578  in
              mk1 uu____58577
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
          let uu____58618 =
            let uu____58621 =
              let uu____58622 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____58622  in
            FStar_Pervasives_Native.Some uu____58621  in
          FStar_Pervasives_Native.Some uu____58618

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
          let uu____58634 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____58634

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_58642  ->
    match uu___436_58642 with
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
    | FStar_Syntax_Syntax.Reflectable uu____58649 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____58650 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____58651 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____58656 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____58665 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____58674 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_58680  ->
    match uu___437_58680 with
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
            (tylid,uvs,bs,t,uu____58723,datacons) ->
            let uu____58733 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____58761,uu____58762,uu____58763,inductive_lid,uu____58765,uu____58766)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____58773 -> failwith "unexpected"))
               in
            (match uu____58733 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____58794 = FStar_Options.print_implicits ()  in
                   if uu____58794 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____58811 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_58818  ->
                             match uu___438_58818 with
                             | FStar_Syntax_Syntax.RecordType uu____58820 ->
                                 true
                             | uu____58830 -> false))
                      in
                   if uu____58811
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____58884,univs1,term,uu____58887,num,uu____58889)
                           ->
                           let uu____58896 =
                             let uu____58897 =
                               FStar_Syntax_Subst.compress term  in
                             uu____58897.FStar_Syntax_Syntax.n  in
                           (match uu____58896 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____58911)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____58980  ->
                                          match uu____58980 with
                                          | (b,qual) ->
                                              let uu____59001 =
                                                bv_as_unique_ident b  in
                                              let uu____59002 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____59001, uu____59002,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____59013 -> failwith "unexpected")
                       | uu____59025 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____59156,num,uu____59158) ->
                            let c =
                              let uu____59179 =
                                let uu____59182 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____59182  in
                              ((l.FStar_Ident.ident), uu____59179,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____59202 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____59282 ->
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
        let uu____59308 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____59308;
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
        let uu____59338 = ts  in
        match uu____59338 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____59351 =
              let uu____59352 =
                let uu____59369 =
                  let uu____59378 =
                    let uu____59385 =
                      let uu____59386 =
                        let uu____59399 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____59399)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____59386  in
                    (uu____59385, FStar_Pervasives_Native.None)  in
                  [uu____59378]  in
                (false, false, uu____59369)  in
              FStar_Parser_AST.Tycon uu____59352  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____59351
  
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
              let uu____59488 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____59488 with
              | (bs,action_defn) ->
                  let uu____59495 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____59495 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____59505 = FStar_Options.print_implicits ()
                            in
                         if uu____59505
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____59515 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____59515 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____59532 =
                             let uu____59543 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____59543,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____59532  in
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
            let uu____59627 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____59627 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____59637 = FStar_Options.print_implicits ()  in
                  if uu____59637 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____59647 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____59647 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59732) ->
          let uu____59741 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____59764 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____59782 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____59790 -> false
                    | uu____59807 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____59741 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____59845 se1 =
                 match uu____59845 with
                 | (datacon_ses1,tycons) ->
                     let uu____59871 = resugar_typ env datacon_ses1 se1  in
                     (match uu____59871 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____59886 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____59886 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____59921 =
                           let uu____59922 =
                             let uu____59923 =
                               let uu____59940 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____59940)  in
                             FStar_Parser_AST.Tycon uu____59923  in
                           decl'_to_decl se uu____59922  in
                         FStar_Pervasives_Native.Some uu____59921
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____59975,uu____59976,uu____59977,uu____59978,uu____59979)
                              ->
                              let uu____59986 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____59986
                          | uu____59989 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____59993 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60000) ->
          let uu____60005 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_60013  ->
                    match uu___439_60013 with
                    | FStar_Syntax_Syntax.Projector (uu____60015,uu____60016)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60018 -> true
                    | uu____60020 -> false))
             in
          if uu____60005
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
             | FStar_Parser_AST.Let (isrec,lets,uu____60055) ->
                 let uu____60084 =
                   let uu____60085 =
                     let uu____60086 =
                       let uu____60097 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____60097)  in
                     FStar_Parser_AST.TopLevelLet uu____60086  in
                   decl'_to_decl se uu____60085  in
                 FStar_Pervasives_Native.Some uu____60084
             | uu____60134 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____60139,fml) ->
          let uu____60141 =
            let uu____60142 =
              let uu____60143 =
                let uu____60148 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____60148)  in
              FStar_Parser_AST.Assume uu____60143  in
            decl'_to_decl se uu____60142  in
          FStar_Pervasives_Native.Some uu____60141
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____60150 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60150
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____60153 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60153
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____60163,t) ->
                let uu____60173 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60173
            | uu____60174 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____60182,t) ->
                let uu____60192 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60192
            | uu____60193 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____60217 -> failwith "Should not happen hopefully"  in
          let uu____60227 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____60227
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____60237 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____60237 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____60249 = FStar_Options.print_implicits ()  in
                 if uu____60249 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____60265 =
                 let uu____60266 =
                   let uu____60267 =
                     let uu____60284 =
                       let uu____60293 =
                         let uu____60300 =
                           let uu____60301 =
                             let uu____60314 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____60314)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____60301  in
                         (uu____60300, FStar_Pervasives_Native.None)  in
                       [uu____60293]  in
                     (false, false, uu____60284)  in
                   FStar_Parser_AST.Tycon uu____60267  in
                 decl'_to_decl se uu____60266  in
               FStar_Pervasives_Native.Some uu____60265)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____60346 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____60346
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____60350 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_60358  ->
                    match uu___440_60358 with
                    | FStar_Syntax_Syntax.Projector (uu____60360,uu____60361)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60363 -> true
                    | uu____60365 -> false))
             in
          if uu____60350
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____60373 =
                 (let uu____60377 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____60377) || (FStar_List.isEmpty uvs)
                  in
               if uu____60373
               then resugar_term' env t
               else
                 (let uu____60382 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____60382 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____60391 = resugar_term' env t1  in
                      label universes uu____60391)
                in
             let uu____60392 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____60392)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____60399 =
            let uu____60400 =
              let uu____60401 =
                let uu____60408 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____60413 = resugar_term' env t  in
                (uu____60408, uu____60413)  in
              FStar_Parser_AST.Splice uu____60401  in
            decl'_to_decl se uu____60400  in
          FStar_Pervasives_Native.Some uu____60399
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____60416 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____60433 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____60449 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____60473 = noenv resugar_term'  in uu____60473 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____60491 = noenv resugar_sigelt'  in uu____60491 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____60509 = noenv resugar_comp'  in uu____60509 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____60532 = noenv resugar_pat'  in uu____60532 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____60566 = noenv resugar_binder'  in uu____60566 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____60591 = noenv resugar_tscheme'  in uu____60591 ts 
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
          let uu____60626 = noenv resugar_eff_decl'  in
          uu____60626 for_free r q ed
  