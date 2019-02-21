open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____16 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____16
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____24 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____24
  
let map_opt :
  'Auu____34 'Auu____35 .
    unit ->
      ('Auu____34 -> 'Auu____35 FStar_Pervasives_Native.option) ->
        'Auu____34 Prims.list -> 'Auu____35 Prims.list
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
         (fun uu___1_129  ->
            match uu___1_129 with
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
          universe_to_int (n1 + (Prims.parse_int "1")) u1
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
      | FStar_Syntax_Syntax.U_succ uu____343 ->
          let uu____344 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____344 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____355 =
                      let uu____356 =
                        let uu____357 =
                          let uu____369 = FStar_Util.string_of_int n1  in
                          (uu____369, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____357  in
                      FStar_Parser_AST.Const uu____356  in
                    mk1 uu____355 r
                | uu____382 ->
                    let e1 =
                      let uu____384 =
                        let uu____385 =
                          let uu____386 =
                            let uu____398 = FStar_Util.string_of_int n1  in
                            (uu____398, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____386  in
                        FStar_Parser_AST.Const uu____385  in
                      mk1 uu____384 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____412 =
                      let uu____413 =
                        let uu____420 = FStar_Ident.id_of_text "+"  in
                        (uu____420, [e1; e2])  in
                      FStar_Parser_AST.Op uu____413  in
                    mk1 uu____412 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____428 ->
               let t =
                 let uu____432 =
                   let uu____433 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____433  in
                 mk1 uu____432 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____442 =
                        let uu____443 =
                          let uu____450 = resugar_universe x r  in
                          (acc, uu____450, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____443  in
                      mk1 uu____442 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____452 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____464 =
              let uu____470 =
                let uu____472 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____472  in
              (uu____470, r)  in
            FStar_Ident.mk_ident uu____464  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___2_510 =
      match uu___2_510 with
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
               let op =
                 let uu____1020 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____1074) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____1020
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
      let uu____1401 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1401 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1471 ->
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
                (let uu____1583 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1583
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1619 =
      let uu____1620 = FStar_Syntax_Subst.compress t  in
      uu____1620.FStar_Syntax_Syntax.n  in
    match uu____1619 with
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
            let uu____1993 =
              let uu____1994 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1994  in
            mk1 uu____1993
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
               | uu____2018 -> failwith "wrong projector format")
            else
              (let uu____2025 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____2029 =
                      let uu____2031 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____2031  in
                    let uu____2034 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____2029 <> uu____2034)
                  in
               if uu____2025
               then
                 let uu____2039 =
                   let uu____2040 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____2040  in
                 mk1 uu____2039
               else
                 (let uu____2043 =
                    let uu____2044 =
                      let uu____2055 = maybe_shorten_fv env fv  in
                      (uu____2055, [])  in
                    FStar_Parser_AST.Construct uu____2044  in
                  mk1 uu____2043))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2073 = FStar_Options.print_universes ()  in
          if uu____2073
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
                   let uu____2104 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2104  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2127 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2135 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2135
          then
            let uu____2138 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2138
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2143 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2164 -> ("Type", true)  in
          (match uu____2143 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2176 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2176  in
               let uu____2177 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2177
               then
                 let uu____2180 =
                   let uu____2181 =
                     let uu____2188 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2188, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2181  in
                 mk1 uu____2180
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2193) ->
          let uu____2218 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2218 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2234 = FStar_Options.print_implicits ()  in
                 if uu____2234 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2272  ->
                         match uu____2272 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2312 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2312 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2322 = FStar_Options.print_implicits ()  in
                 if uu____2322 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2333 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2333 FStar_List.rev  in
               let rec aux body3 uu___3_2358 =
                 match uu___3_2358 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2374 =
            let uu____2379 =
              let uu____2380 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2380]  in
            FStar_Syntax_Subst.open_term uu____2379 phi  in
          (match uu____2374 with
           | (x1,phi1) ->
               let b =
                 let uu____2402 =
                   let uu____2405 = FStar_List.hd x1  in
                   resugar_binder' env uu____2405 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2402  in
               let uu____2412 =
                 let uu____2413 =
                   let uu____2418 = resugar_term' env phi1  in
                   (b, uu____2418)  in
                 FStar_Parser_AST.Refine uu____2413  in
               mk1 uu____2412)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2420;
             FStar_Syntax_Syntax.vars = uu____2421;_},(e,uu____2423)::[])
          when
          (let uu____2464 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2464) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___4_2513 =
            match uu___4_2513 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2583 -> failwith "last of an empty list"  in
          let rec last_two uu___5_2622 =
            match uu___5_2622 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____2654::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2732::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2803  ->
                   match uu____2803 with
                   | (e2,qual) ->
                       let uu____2820 = resugar_term' env e2  in
                       let uu____2821 = resugar_imp env qual  in
                       (uu____2820, uu____2821)) args1
               in
            let uu____2822 = resugar_term' env e1  in
            match uu____2822 with
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
                     fun uu____2859  ->
                       match uu____2859 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2875 = FStar_Options.print_implicits ()  in
            if uu____2875 then args else filter_imp args  in
          let uu____2890 = resugar_term_as_op e  in
          (match uu____2890 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2903) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2928  ->
                        match uu____2928 with
                        | (x,uu____2940) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2949 =
                                   let uu____2950 =
                                     let uu____2951 =
                                       let uu____2958 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2958, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2951  in
                                   mk1 uu____2950  in
                                 FStar_Pervasives_Native.Some uu____2949))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2962) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2988)::[] -> b
                 | uu____3005 -> failwith "wrong arguments to dtuple"  in
               let uu____3015 =
                 let uu____3016 = FStar_Syntax_Subst.compress body  in
                 uu____3016.FStar_Syntax_Syntax.n  in
               (match uu____3015 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3021) ->
                    let uu____3046 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3046 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3056 = FStar_Options.print_implicits ()
                              in
                           if uu____3056 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3073 =
                           let uu____3074 =
                             let uu____3085 =
                               FStar_List.map
                                 (fun _0_1  -> FStar_Util.Inl _0_1) xs3
                                in
                             (uu____3085, body3)  in
                           FStar_Parser_AST.Sum uu____3074  in
                         mk1 uu____3073)
                | uu____3102 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3125  ->
                              match uu____3125 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3143) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3152) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3161 = FStar_List.hd args1  in
               (match uu____3161 with
                | (t1,uu____3175) ->
                    let uu____3180 =
                      let uu____3181 = FStar_Syntax_Subst.compress t1  in
                      uu____3181.FStar_Syntax_Syntax.n  in
                    (match uu____3180 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3188 =
                           let uu____3189 =
                             let uu____3194 = resugar_term' env t1  in
                             (uu____3194, f)  in
                           FStar_Parser_AST.Project uu____3189  in
                         mk1 uu____3188
                     | uu____3195 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3196) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____3220 =
                 match new_args with
                 | (a1,uu____3230)::(a2,uu____3232)::[] -> (a1, a2)
                 | uu____3259 -> failwith "wrong arguments to try_with"  in
               (match uu____3220 with
                | (body,handler) ->
                    let decomp term =
                      let uu____3281 =
                        let uu____3282 = FStar_Syntax_Subst.compress term  in
                        uu____3282.FStar_Syntax_Syntax.n  in
                      match uu____3281 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____3287) ->
                          let uu____3312 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____3312 with | (x1,e2) -> e2)
                      | uu____3319 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____3322 = decomp body  in
                      resugar_term' env uu____3322  in
                    let handler1 =
                      let uu____3324 = decomp handler  in
                      resugar_term' env uu____3324  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____3332,uu____3333,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____3365,uu____3366,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____3403 =
                            let uu____3404 =
                              let uu____3413 = resugar_body t11  in
                              (uu____3413, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____3404  in
                          mk1 uu____3403
                      | uu____3416 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____3474 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____3504) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3513) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3534) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3632 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3645 =
                   let uu____3646 = FStar_Syntax_Subst.compress body  in
                   uu____3646.FStar_Syntax_Syntax.n  in
                 match uu____3645 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3651) ->
                     let uu____3676 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3676 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3686 = FStar_Options.print_implicits ()
                               in
                            if uu____3686 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3702 =
                            let uu____3711 =
                              let uu____3712 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3712.FStar_Syntax_Syntax.n  in
                            match uu____3711 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3730 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____3760 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3804  ->
                                                     match uu____3804 with
                                                     | (e2,uu____3812) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3760, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3828 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3828)
                                  | uu____3837 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3730 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3869 ->
                                let uu____3870 = resugar_term' env body2  in
                                ([], uu____3870)
                             in
                          (match uu____3702 with
                           | (pats,body3) ->
                               let uu____3887 = uncurry xs3 pats body3  in
                               (match uu____3887 with
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
                 | uu____3939 ->
                     if op = "forall"
                     then
                       let uu____3943 =
                         let uu____3944 =
                           let uu____3957 = resugar_term' env body  in
                           ([], [[]], uu____3957)  in
                         FStar_Parser_AST.QForall uu____3944  in
                       mk1 uu____3943
                     else
                       (let uu____3970 =
                          let uu____3971 =
                            let uu____3984 = resugar_term' env body  in
                            ([], [[]], uu____3984)  in
                          FStar_Parser_AST.QExists uu____3971  in
                        mk1 uu____3970)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4013)::[] -> resugar b
                  | uu____4030 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4042) ->
               let uu____4050 = FStar_List.hd args1  in
               (match uu____4050 with
                | (e1,uu____4064) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4136  ->
                         match uu____4136 with
                         | (e1,qual) ->
                             let uu____4153 = resugar_term' env e1  in
                             let uu____4154 = resugar_imp env qual  in
                             (uu____4153, uu____4154)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4170 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4170 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4218 =
                               let uu____4219 =
                                 let uu____4226 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4226)  in
                               FStar_Parser_AST.Op uu____4219  in
                             mk1 uu____4218  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4244  ->
                                  match uu____4244 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4263 =
                      let uu____4264 =
                        let uu____4271 =
                          let uu____4274 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4274
                           in
                        (op1, uu____4271)  in
                      FStar_Parser_AST.Op uu____4264  in
                    mk1 uu____4263
                | uu____4287 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4356 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4356 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4402 =
                   let uu____4415 =
                     let uu____4420 = resugar_pat' env pat1 branch_bv  in
                     let uu____4421 = resugar_term' env e  in
                     (uu____4420, uu____4421)  in
                   (FStar_Pervasives_Native.None, uu____4415)  in
                 [uu____4402]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4473,t1)::(pat2,uu____4476,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4572 =
            let uu____4573 =
              let uu____4580 = resugar_term' env e  in
              let uu____4581 = resugar_term' env t1  in
              let uu____4582 = resugar_term' env t2  in
              (uu____4580, uu____4581, uu____4582)  in
            FStar_Parser_AST.If uu____4573  in
          mk1 uu____4572
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4648 =
            match uu____4648 with
            | (pat,wopt,b) ->
                let uu____4690 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4690 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4742 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4742
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4746 =
            let uu____4747 =
              let uu____4762 = resugar_term' env e  in
              let uu____4763 = FStar_List.map resugar_branch branches  in
              (uu____4762, uu____4763)  in
            FStar_Parser_AST.Match uu____4747  in
          mk1 uu____4746
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4809) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4878 =
            let uu____4879 =
              let uu____4888 = resugar_term' env e  in
              (uu____4888, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4879  in
          mk1 uu____4878
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4917 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4917 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4971 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4971
                    in
                 let uu____4978 =
                   let uu____4983 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4983
                    in
                 match uu____4978 with
                 | (univs1,td) ->
                     let uu____5003 =
                       let uu____5010 =
                         let uu____5011 = FStar_Syntax_Subst.compress td  in
                         uu____5011.FStar_Syntax_Syntax.n  in
                       match uu____5010 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5020,(t1,uu____5022)::(d,uu____5024)::[])
                           -> (t1, d)
                       | uu____5081 -> failwith "wrong let binding format"
                        in
                     (match uu____5003 with
                      | (typ,def) ->
                          let uu____5112 =
                            let uu____5128 =
                              let uu____5129 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5129.FStar_Syntax_Syntax.n  in
                            match uu____5128 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5149) ->
                                let uu____5174 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5174 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5205 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5205
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5228 -> ([], def, false)  in
                          (match uu____5112 with
                           | (binders,term,is_pat_app) ->
                               let uu____5283 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5294 =
                                       let uu____5295 =
                                         let uu____5296 =
                                           let uu____5303 =
                                             bv_as_unique_ident bv  in
                                           (uu____5303,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5296
                                          in
                                       mk_pat uu____5295  in
                                     (uu____5294, term)
                                  in
                               (match uu____5283 with
                                | (pat,term1) ->
                                    let uu____5325 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5368  ->
                                                  match uu____5368 with
                                                  | (bv,q) ->
                                                      let uu____5383 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5383
                                                        (fun q1  ->
                                                           let uu____5395 =
                                                             let uu____5396 =
                                                               let uu____5403
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5403,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5396
                                                              in
                                                           mk_pat uu____5395)))
                                           in
                                        let uu____5406 =
                                          let uu____5411 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5411)
                                           in
                                        let uu____5414 =
                                          universe_to_string univs1  in
                                        (uu____5406, uu____5414)
                                      else
                                        (let uu____5423 =
                                           let uu____5428 =
                                             resugar_term' env term1  in
                                           (pat, uu____5428)  in
                                         let uu____5429 =
                                           universe_to_string univs1  in
                                         (uu____5423, uu____5429))
                                       in
                                    (attrs_opt, uu____5325))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5535 =
                   match uu____5535 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5595 =
                         let uu____5597 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5597  in
                       if uu____5595
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5678) ->
          let s =
            let uu____5697 =
              let uu____5699 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5699 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5697  in
          let uu____5704 = mk1 FStar_Parser_AST.Wild  in label s uu____5704
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5712 =
            let uu____5713 =
              let uu____5718 = resugar_term' env tm  in (uu____5718, qi1)  in
            FStar_Parser_AST.Quote uu____5713  in
          mk1 uu____5712
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___6_5730 =
            match uu___6_5730 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5738,(uu____5739,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____5800 =
                        let uu____5801 =
                          let uu____5810 = resugar_seq t11  in
                          (uu____5810, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____5801  in
                      mk1 uu____5800
                  | uu____5813 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5857  ->
                         match uu____5857 with
                         | (x,uu____5865) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____5870 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5888,t1) ->
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
               let uu____5928 = FStar_Options.print_universes ()  in
               if uu____5928
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
               let uu____5992 = FStar_Options.print_universes ()  in
               if uu____5992
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
            let uu____6036 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6036, FStar_Parser_AST.Nothing)  in
          let uu____6037 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6037
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6060 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6060
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6145 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6145, (FStar_Pervasives_Native.snd post))  in
                    let uu____6156 =
                      let uu____6165 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6165 then [] else [pre]  in
                    let uu____6200 =
                      let uu____6209 =
                        let uu____6218 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6218 then [] else [pats]  in
                      FStar_List.append [post1] uu____6209  in
                    FStar_List.append uu____6156 uu____6200
                | uu____6277 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6311  ->
                   match uu____6311 with
                   | (e,uu____6323) ->
                       let uu____6328 = resugar_term' env e  in
                       (uu____6328, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___7_6353 =
              match uu___7_6353 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6386 = resugar_term' env e  in
                         (uu____6386, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6391 -> aux l tl1)
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
        let uu____6438 = b  in
        match uu____6438 with
        | (x,aq) ->
            let uu____6447 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6447
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6461 =
                       let uu____6462 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6462  in
                     FStar_Parser_AST.mk_binder uu____6461 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6463 ->
                     let uu____6464 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6464
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6469 =
                          let uu____6470 =
                            let uu____6475 = bv_as_unique_ident x  in
                            (uu____6475, e)  in
                          FStar_Parser_AST.Annotated uu____6470  in
                        FStar_Parser_AST.mk_binder uu____6469 r
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
              let uu____6495 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6495  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6499 =
                if used
                then
                  let uu____6501 =
                    let uu____6508 = bv_as_unique_ident v1  in
                    (uu____6508, aqual)  in
                  FStar_Parser_AST.PatVar uu____6501
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6499  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6515;
                  FStar_Syntax_Syntax.vars = uu____6516;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6526 = FStar_Options.print_bound_var_types ()  in
                if uu____6526
                then
                  let uu____6529 =
                    let uu____6530 =
                      let uu____6541 =
                        let uu____6548 = resugar_term' env typ  in
                        (uu____6548, FStar_Pervasives_Native.None)  in
                      (pat, uu____6541)  in
                    FStar_Parser_AST.PatAscribed uu____6530  in
                  mk1 uu____6529
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
          let uu____6569 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6569
            (fun aqual  ->
               let uu____6581 =
                 let uu____6586 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                   uu____6586
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6581)

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
          (let uu____6658 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6658) &&
            (let uu____6661 =
               FStar_List.existsML
                 (fun uu____6674  ->
                    match uu____6674 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6696)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6701 -> false
                          | uu____6703 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6661)
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
            let uu____6771 = may_drop_implicits args  in
            if uu____6771 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6796  ->
                 match uu____6796 with
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
              ((let uu____6851 =
                  let uu____6853 =
                    let uu____6855 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6855  in
                  Prims.op_Negation uu____6853  in
                if uu____6851
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
              let uu____6899 = filter_pattern_imp args  in
              (match uu____6899 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____6949 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____6949 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6968 =
                       let uu____6974 =
                         let uu____6976 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6976
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6974)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6968);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7029  ->
                        match uu____7029 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7046 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7046)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7054;
                 FStar_Syntax_Syntax.fv_delta = uu____7055;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7084 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7084 FStar_List.rev  in
              let args1 =
                let uu____7100 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7120  ->
                          match uu____7120 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7100 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7198 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7198
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7221 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7221
                 in
              let args2 =
                let uu____7239 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7239 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7283 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7283 with
               | FStar_Pervasives_Native.Some (op,uu____7295) ->
                   let uu____7312 =
                     let uu____7313 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7313  in
                   mk1 uu____7312
               | FStar_Pervasives_Native.None  ->
                   let uu____7323 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7323 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7328 ->
              let uu____7329 =
                let uu____7330 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7330  in
              mk1 uu____7329
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
          let uu____7370 =
            let uu____7373 =
              let uu____7374 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7374  in
            FStar_Pervasives_Native.Some uu____7373  in
          FStar_Pervasives_Native.Some uu____7370

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
          let uu____7386 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7386

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___8_7394  ->
    match uu___8_7394 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7401 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7402 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7403 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7408 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7417 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7426 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___9_7432  ->
    match uu___9_7432 with
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
            (tylid,uvs,bs,t,uu____7475,datacons) ->
            let uu____7485 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7513,uu____7514,uu____7515,inductive_lid,uu____7517,uu____7518)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7525 -> failwith "unexpected"))
               in
            (match uu____7485 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7546 = FStar_Options.print_implicits ()  in
                   if uu____7546 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7563 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___10_7570  ->
                             match uu___10_7570 with
                             | FStar_Syntax_Syntax.RecordType uu____7572 ->
                                 true
                             | uu____7582 -> false))
                      in
                   if uu____7563
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7636,univs1,term,uu____7639,num,uu____7641)
                           ->
                           let uu____7648 =
                             let uu____7649 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7649.FStar_Syntax_Syntax.n  in
                           (match uu____7648 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7663)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7732  ->
                                          match uu____7732 with
                                          | (b,qual) ->
                                              let uu____7753 =
                                                bv_as_unique_ident b  in
                                              let uu____7754 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____7753, uu____7754,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____7765 -> failwith "unexpected")
                       | uu____7777 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____7908,num,uu____7910) ->
                            let c =
                              let uu____7931 =
                                let uu____7934 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____7934  in
                              ((l.FStar_Ident.ident), uu____7931,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____7954 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8034 ->
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
        let uu____8060 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8060;
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
        let uu____8090 = ts  in
        match uu____8090 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8103 =
              let uu____8104 =
                let uu____8121 =
                  let uu____8130 =
                    let uu____8137 =
                      let uu____8138 =
                        let uu____8151 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8151)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8138  in
                    (uu____8137, FStar_Pervasives_Native.None)  in
                  [uu____8130]  in
                (false, false, uu____8121)  in
              FStar_Parser_AST.Tycon uu____8104  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8103
  
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
              let uu____8240 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____8240 with
              | (bs,action_defn) ->
                  let uu____8247 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____8247 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____8257 = FStar_Options.print_implicits ()
                            in
                         if uu____8257
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____8267 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____8267 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____8284 =
                             let uu____8295 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____8295,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____8284  in
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
            let uu____8379 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____8379 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____8389 = FStar_Options.print_implicits ()  in
                  if uu____8389 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____8399 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____8399 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8484) ->
          let uu____8493 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8516 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8534 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8542 -> false
                    | uu____8559 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8493 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8597 se1 =
                 match uu____8597 with
                 | (datacon_ses1,tycons) ->
                     let uu____8623 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8623 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8638 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8638 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8673 =
                           let uu____8674 =
                             let uu____8675 =
                               let uu____8692 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____8692)  in
                             FStar_Parser_AST.Tycon uu____8675  in
                           decl'_to_decl se uu____8674  in
                         FStar_Pervasives_Native.Some uu____8673
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8727,uu____8728,uu____8729,uu____8730,uu____8731)
                              ->
                              let uu____8738 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8738
                          | uu____8741 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8745 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8752) ->
          let uu____8757 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___11_8765  ->
                    match uu___11_8765 with
                    | FStar_Syntax_Syntax.Projector (uu____8767,uu____8768)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8770 -> true
                    | uu____8772 -> false))
             in
          if uu____8757
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
             | FStar_Parser_AST.Let (isrec,lets,uu____8807) ->
                 let uu____8836 =
                   let uu____8837 =
                     let uu____8838 =
                       let uu____8849 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____8849)  in
                     FStar_Parser_AST.TopLevelLet uu____8838  in
                   decl'_to_decl se uu____8837  in
                 FStar_Pervasives_Native.Some uu____8836
             | uu____8886 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____8891,fml) ->
          let uu____8893 =
            let uu____8894 =
              let uu____8895 =
                let uu____8900 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____8900)  in
              FStar_Parser_AST.Assume uu____8895  in
            decl'_to_decl se uu____8894  in
          FStar_Pervasives_Native.Some uu____8893
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____8902 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8902
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____8905 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8905
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____8915,t) ->
                let uu____8925 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8925
            | uu____8926 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____8934,t) ->
                let uu____8944 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8944
            | uu____8945 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____8969 -> failwith "Should not happen hopefully"  in
          let uu____8979 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____8979
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____8989 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8989 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9001 = FStar_Options.print_implicits ()  in
                 if uu____9001 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9017 =
                 let uu____9018 =
                   let uu____9019 =
                     let uu____9036 =
                       let uu____9045 =
                         let uu____9052 =
                           let uu____9053 =
                             let uu____9066 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9066)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9053  in
                         (uu____9052, FStar_Pervasives_Native.None)  in
                       [uu____9045]  in
                     (false, false, uu____9036)  in
                   FStar_Parser_AST.Tycon uu____9019  in
                 decl'_to_decl se uu____9018  in
               FStar_Pervasives_Native.Some uu____9017)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9098 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9098
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9102 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___12_9110  ->
                    match uu___12_9110 with
                    | FStar_Syntax_Syntax.Projector (uu____9112,uu____9113)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9115 -> true
                    | uu____9117 -> false))
             in
          if uu____9102
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9125 =
                 (let uu____9129 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9129) || (FStar_List.isEmpty uvs)
                  in
               if uu____9125
               then resugar_term' env t
               else
                 (let uu____9134 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9134 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9143 = resugar_term' env t1  in
                      label universes uu____9143)
                in
             let uu____9144 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9144)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9151 =
            let uu____9152 =
              let uu____9153 =
                let uu____9160 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9165 = resugar_term' env t  in
                (uu____9160, uu____9165)  in
              FStar_Parser_AST.Splice uu____9153  in
            decl'_to_decl se uu____9152  in
          FStar_Pervasives_Native.Some uu____9151
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9168 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9185 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9201 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9225 = noenv resugar_term'  in uu____9225 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9243 = noenv resugar_sigelt'  in uu____9243 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9261 = noenv resugar_comp'  in uu____9261 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9284 = noenv resugar_pat'  in uu____9284 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9318 = noenv resugar_binder'  in uu____9318 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9343 = noenv resugar_tscheme'  in uu____9343 ts 
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
          let uu____9378 = noenv resugar_eff_decl'  in
          uu____9378 for_free r q ed
  