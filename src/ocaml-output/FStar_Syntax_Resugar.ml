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
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
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
         (fun uu___198_129  ->
            match uu___198_129 with
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
    let name_of_op uu___199_510 =
      match uu___199_510 with
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
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____918 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____936 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____936 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____954 ->
               let op =
                 let uu____960 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____1014) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____960
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
      (FStar_Parser_Const.strcat_lid, "^");
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
      let uu____1348 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1348 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1418 ->
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
                (let uu____1530 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1530
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1566 =
      let uu____1567 = FStar_Syntax_Subst.compress t  in
      uu____1567.FStar_Syntax_Syntax.n  in
    match uu____1566 with
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
        let uu____1598 = string_to_op s  in
        (match uu____1598 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1638 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1655 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1672 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1683 -> true
    | uu____1685 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1706 ->
        let uu____1708 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1708
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1722 = may_shorten lid  in
      if uu____1722 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1867 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1867  in
      let uu____1870 =
        let uu____1871 = FStar_Syntax_Subst.compress t  in
        uu____1871.FStar_Syntax_Syntax.n  in
      match uu____1870 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1874 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1899 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1899
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1902 =
              let uu____1905 = bv_as_unique_ident x  in [uu____1905]  in
            FStar_Ident.lid_of_ids uu____1902  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1908 =
              let uu____1911 = bv_as_unique_ident x  in [uu____1911]  in
            FStar_Ident.lid_of_ids uu____1908  in
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
          let is_prefix = Prims.strcat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____1940 =
              let uu____1941 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1941  in
            mk1 uu____1940
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
               | uu____1965 -> failwith "wrong projector format")
            else
              (let uu____1972 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1976 =
                      let uu____1978 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1978  in
                    let uu____1981 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1976 <> uu____1981)
                  in
               if uu____1972
               then
                 let uu____1986 =
                   let uu____1987 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1987  in
                 mk1 uu____1986
               else
                 (let uu____1990 =
                    let uu____1991 =
                      let uu____2002 = maybe_shorten_fv env fv  in
                      (uu____2002, [])  in
                    FStar_Parser_AST.Construct uu____1991  in
                  mk1 uu____1990))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2020 = FStar_Options.print_universes ()  in
          if uu____2020
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
                   let uu____2051 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2051  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2074 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2082 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2082
          then
            let uu____2085 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2085
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2090 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2111 -> ("Type", true)  in
          (match uu____2090 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2123 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2123  in
               let uu____2124 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2124
               then
                 let uu____2127 =
                   let uu____2128 =
                     let uu____2135 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2135, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2128  in
                 mk1 uu____2127
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2140) ->
          let uu____2165 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2165 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2181 = FStar_Options.print_implicits ()  in
                 if uu____2181 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2219  ->
                         match uu____2219 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2259 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2259 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2269 = FStar_Options.print_implicits ()  in
                 if uu____2269 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2280 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2280 FStar_List.rev  in
               let rec aux body3 uu___200_2305 =
                 match uu___200_2305 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2321 =
            let uu____2326 =
              let uu____2327 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2327]  in
            FStar_Syntax_Subst.open_term uu____2326 phi  in
          (match uu____2321 with
           | (x1,phi1) ->
               let b =
                 let uu____2349 =
                   let uu____2352 = FStar_List.hd x1  in
                   resugar_binder' env uu____2352 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2349  in
               let uu____2359 =
                 let uu____2360 =
                   let uu____2365 = resugar_term' env phi1  in
                   (b, uu____2365)  in
                 FStar_Parser_AST.Refine uu____2360  in
               mk1 uu____2359)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2367;
             FStar_Syntax_Syntax.vars = uu____2368;_},(e,uu____2370)::[])
          when
          (let uu____2411 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2411) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___201_2460 =
            match uu___201_2460 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2530 -> failwith "last of an empty list"  in
          let rec last_two uu___202_2569 =
            match uu___202_2569 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____2601::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2679::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2750  ->
                   match uu____2750 with
                   | (e2,qual) ->
                       let uu____2767 = resugar_term' env e2  in
                       let uu____2768 = resugar_imp env qual  in
                       (uu____2767, uu____2768)) args1
               in
            let uu____2769 = resugar_term' env e1  in
            match uu____2769 with
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
                     fun uu____2806  ->
                       match uu____2806 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2822 = FStar_Options.print_implicits ()  in
            if uu____2822 then args else filter_imp args  in
          let uu____2837 = resugar_term_as_op e  in
          (match uu____2837 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2850) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2875  ->
                        match uu____2875 with
                        | (x,uu____2887) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2896 =
                                   let uu____2897 =
                                     let uu____2898 =
                                       let uu____2905 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2905, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2898  in
                                   mk1 uu____2897  in
                                 FStar_Pervasives_Native.Some uu____2896))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2909) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2935)::[] -> b
                 | uu____2952 -> failwith "wrong arguments to dtuple"  in
               let uu____2962 =
                 let uu____2963 = FStar_Syntax_Subst.compress body  in
                 uu____2963.FStar_Syntax_Syntax.n  in
               (match uu____2962 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2968) ->
                    let uu____2993 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2993 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3003 = FStar_Options.print_implicits ()
                              in
                           if uu____3003 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3020 =
                           let uu____3021 =
                             let uu____3032 =
                               FStar_List.map
                                 (fun _0_1  -> FStar_Util.Inl _0_1) xs3
                                in
                             (uu____3032, body3)  in
                           FStar_Parser_AST.Sum uu____3021  in
                         mk1 uu____3020)
                | uu____3049 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3072  ->
                              match uu____3072 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3090) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3099) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3108 = FStar_List.hd args1  in
               (match uu____3108 with
                | (t1,uu____3122) ->
                    let uu____3127 =
                      let uu____3128 = FStar_Syntax_Subst.compress t1  in
                      uu____3128.FStar_Syntax_Syntax.n  in
                    (match uu____3127 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3135 =
                           let uu____3136 =
                             let uu____3141 = resugar_term' env t1  in
                             (uu____3141, f)  in
                           FStar_Parser_AST.Project uu____3136  in
                         mk1 uu____3135
                     | uu____3142 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3143) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____3167 =
                 match new_args with
                 | (a1,uu____3177)::(a2,uu____3179)::[] -> (a1, a2)
                 | uu____3206 -> failwith "wrong arguments to try_with"  in
               (match uu____3167 with
                | (body,handler) ->
                    let decomp term =
                      let uu____3228 =
                        let uu____3229 = FStar_Syntax_Subst.compress term  in
                        uu____3229.FStar_Syntax_Syntax.n  in
                      match uu____3228 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____3234) ->
                          let uu____3259 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____3259 with | (x1,e2) -> e2)
                      | uu____3266 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____3269 = decomp body  in
                      resugar_term' env uu____3269  in
                    let handler1 =
                      let uu____3271 = decomp handler  in
                      resugar_term' env uu____3271  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____3279,uu____3280,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____3312,uu____3313,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____3350 =
                            let uu____3351 =
                              let uu____3360 = resugar_body t11  in
                              (uu____3360, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____3351  in
                          mk1 uu____3350
                      | uu____3363 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____3421 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____3451) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3460) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3481) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3579 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3592 =
                   let uu____3593 = FStar_Syntax_Subst.compress body  in
                   uu____3593.FStar_Syntax_Syntax.n  in
                 match uu____3592 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3598) ->
                     let uu____3623 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3623 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3633 = FStar_Options.print_implicits ()
                               in
                            if uu____3633 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3649 =
                            let uu____3658 =
                              let uu____3659 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3659.FStar_Syntax_Syntax.n  in
                            match uu____3658 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3677 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____3707 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3751  ->
                                                     match uu____3751 with
                                                     | (e2,uu____3759) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3707, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3775 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3775)
                                  | uu____3784 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3677 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3816 ->
                                let uu____3817 = resugar_term' env body2  in
                                ([], uu____3817)
                             in
                          (match uu____3649 with
                           | (pats,body3) ->
                               let uu____3834 = uncurry xs3 pats body3  in
                               (match uu____3834 with
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
                 | uu____3886 ->
                     if op = "forall"
                     then
                       let uu____3890 =
                         let uu____3891 =
                           let uu____3904 = resugar_term' env body  in
                           ([], [[]], uu____3904)  in
                         FStar_Parser_AST.QForall uu____3891  in
                       mk1 uu____3890
                     else
                       (let uu____3917 =
                          let uu____3918 =
                            let uu____3931 = resugar_term' env body  in
                            ([], [[]], uu____3931)  in
                          FStar_Parser_AST.QExists uu____3918  in
                        mk1 uu____3917)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3960)::[] -> resugar b
                  | uu____3977 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3989) ->
               let uu____3997 = FStar_List.hd args1  in
               (match uu____3997 with
                | (e1,uu____4011) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4083  ->
                         match uu____4083 with
                         | (e1,qual) ->
                             let uu____4100 = resugar_term' env e1  in
                             let uu____4101 = resugar_imp env qual  in
                             (uu____4100, uu____4101)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4117 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4117 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4165 =
                               let uu____4166 =
                                 let uu____4173 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4173)  in
                               FStar_Parser_AST.Op uu____4166  in
                             mk1 uu____4165  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4191  ->
                                  match uu____4191 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4210 =
                      let uu____4211 =
                        let uu____4218 =
                          let uu____4221 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4221
                           in
                        (op1, uu____4218)  in
                      FStar_Parser_AST.Op uu____4211  in
                    mk1 uu____4210
                | uu____4234 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4303 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4303 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4349 =
                   let uu____4362 =
                     let uu____4367 = resugar_pat' env pat1 branch_bv  in
                     let uu____4368 = resugar_term' env e  in
                     (uu____4367, uu____4368)  in
                   (FStar_Pervasives_Native.None, uu____4362)  in
                 [uu____4349]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4420,t1)::(pat2,uu____4423,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4519 =
            let uu____4520 =
              let uu____4527 = resugar_term' env e  in
              let uu____4528 = resugar_term' env t1  in
              let uu____4529 = resugar_term' env t2  in
              (uu____4527, uu____4528, uu____4529)  in
            FStar_Parser_AST.If uu____4520  in
          mk1 uu____4519
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4595 =
            match uu____4595 with
            | (pat,wopt,b) ->
                let uu____4637 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4637 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4689 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4689
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4693 =
            let uu____4694 =
              let uu____4709 = resugar_term' env e  in
              let uu____4710 = FStar_List.map resugar_branch branches  in
              (uu____4709, uu____4710)  in
            FStar_Parser_AST.Match uu____4694  in
          mk1 uu____4693
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4756) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4825 =
            let uu____4826 =
              let uu____4835 = resugar_term' env e  in
              (uu____4835, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4826  in
          mk1 uu____4825
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4864 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4864 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4918 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4918
                    in
                 let uu____4925 =
                   let uu____4930 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4930
                    in
                 match uu____4925 with
                 | (univs1,td) ->
                     let uu____4950 =
                       let uu____4957 =
                         let uu____4958 = FStar_Syntax_Subst.compress td  in
                         uu____4958.FStar_Syntax_Syntax.n  in
                       match uu____4957 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4967,(t1,uu____4969)::(d,uu____4971)::[])
                           -> (t1, d)
                       | uu____5028 -> failwith "wrong let binding format"
                        in
                     (match uu____4950 with
                      | (typ,def) ->
                          let uu____5059 =
                            let uu____5075 =
                              let uu____5076 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5076.FStar_Syntax_Syntax.n  in
                            match uu____5075 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5096) ->
                                let uu____5121 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5121 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5152 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5152
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5175 -> ([], def, false)  in
                          (match uu____5059 with
                           | (binders,term,is_pat_app) ->
                               let uu____5230 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5241 =
                                       let uu____5242 =
                                         let uu____5243 =
                                           let uu____5250 =
                                             bv_as_unique_ident bv  in
                                           (uu____5250,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5243
                                          in
                                       mk_pat uu____5242  in
                                     (uu____5241, term)
                                  in
                               (match uu____5230 with
                                | (pat,term1) ->
                                    let uu____5272 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5315  ->
                                                  match uu____5315 with
                                                  | (bv,q) ->
                                                      let uu____5330 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5330
                                                        (fun q1  ->
                                                           let uu____5342 =
                                                             let uu____5343 =
                                                               let uu____5350
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5350,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5343
                                                              in
                                                           mk_pat uu____5342)))
                                           in
                                        let uu____5353 =
                                          let uu____5358 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5358)
                                           in
                                        let uu____5361 =
                                          universe_to_string univs1  in
                                        (uu____5353, uu____5361)
                                      else
                                        (let uu____5370 =
                                           let uu____5375 =
                                             resugar_term' env term1  in
                                           (pat, uu____5375)  in
                                         let uu____5376 =
                                           universe_to_string univs1  in
                                         (uu____5370, uu____5376))
                                       in
                                    (attrs_opt, uu____5272))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5482 =
                   match uu____5482 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5542 =
                         let uu____5544 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5544  in
                       if uu____5542
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5625) ->
          let s =
            let uu____5644 =
              let uu____5646 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5646 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____5644  in
          let uu____5651 = mk1 FStar_Parser_AST.Wild  in label s uu____5651
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5659 =
            let uu____5660 =
              let uu____5665 = resugar_term' env tm  in (uu____5665, qi1)  in
            FStar_Parser_AST.Quote uu____5660  in
          mk1 uu____5659
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___203_5677 =
            match uu___203_5677 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5685,(uu____5686,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____5747 =
                        let uu____5748 =
                          let uu____5757 = resugar_seq t11  in
                          (uu____5757, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____5748  in
                      mk1 uu____5747
                  | uu____5760 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5804  ->
                         match uu____5804 with
                         | (x,uu____5812) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____5817 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____5834 =
                 let uu____5835 =
                   let uu____5844 = resugar_term' env e  in
                   let uu____5845 =
                     let uu____5846 =
                       let uu____5847 =
                         let uu____5858 =
                           let uu____5865 =
                             let uu____5870 = resugar_term' env t1  in
                             (uu____5870, FStar_Parser_AST.Nothing)  in
                           [uu____5865]  in
                         (name1, uu____5858)  in
                       FStar_Parser_AST.Construct uu____5847  in
                     mk1 uu____5846  in
                   (uu____5844, uu____5845, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5835  in
               mk1 uu____5834
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5888,t1) ->
               let uu____5894 =
                 let uu____5895 =
                   let uu____5904 = resugar_term' env e  in
                   let uu____5905 =
                     let uu____5906 =
                       let uu____5907 =
                         let uu____5918 =
                           let uu____5925 =
                             let uu____5930 = resugar_term' env t1  in
                             (uu____5930, FStar_Parser_AST.Nothing)  in
                           [uu____5925]  in
                         (name1, uu____5918)  in
                       FStar_Parser_AST.Construct uu____5907  in
                     mk1 uu____5906  in
                   (uu____5904, uu____5905, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5895  in
               mk1 uu____5894)
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
               let uu____5981 = FStar_Options.print_universes ()  in
               if uu____5981
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
               let uu____6045 = FStar_Options.print_universes ()  in
               if uu____6045
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
            let uu____6089 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6089, FStar_Parser_AST.Nothing)  in
          let uu____6090 = FStar_Options.print_effect_args ()  in
          if uu____6090
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6113 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6113
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6198 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6198, (FStar_Pervasives_Native.snd post))  in
                    let uu____6209 =
                      let uu____6218 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6218 then [] else [pre]  in
                    let uu____6253 =
                      let uu____6262 =
                        let uu____6271 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6271 then [] else [pats]  in
                      FStar_List.append [post1] uu____6262  in
                    FStar_List.append uu____6209 uu____6253
                | uu____6330 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6364  ->
                   match uu____6364 with
                   | (e,uu____6376) ->
                       let uu____6381 = resugar_term' env e  in
                       (uu____6381, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___204_6406 =
              match uu___204_6406 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6439 = resugar_term' env e  in
                         (uu____6439, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6444 -> aux l tl1)
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
        let uu____6491 = b  in
        match uu____6491 with
        | (x,aq) ->
            let uu____6500 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6500
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6514 =
                       let uu____6515 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6515  in
                     FStar_Parser_AST.mk_binder uu____6514 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6516 ->
                     let uu____6517 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6517
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6522 =
                          let uu____6523 =
                            let uu____6528 = bv_as_unique_ident x  in
                            (uu____6528, e)  in
                          FStar_Parser_AST.Annotated uu____6523  in
                        FStar_Parser_AST.mk_binder uu____6522 r
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
              let uu____6548 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6548  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6552 =
                if used
                then
                  let uu____6554 =
                    let uu____6561 = bv_as_unique_ident v1  in
                    (uu____6561, aqual)  in
                  FStar_Parser_AST.PatVar uu____6554
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6552  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6568;
                  FStar_Syntax_Syntax.vars = uu____6569;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6579 = FStar_Options.print_bound_var_types ()  in
                if uu____6579
                then
                  let uu____6582 =
                    let uu____6583 =
                      let uu____6594 =
                        let uu____6601 = resugar_term' env typ  in
                        (uu____6601, FStar_Pervasives_Native.None)  in
                      (pat, uu____6594)  in
                    FStar_Parser_AST.PatAscribed uu____6583  in
                  mk1 uu____6582
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
          let uu____6622 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6622
            (fun aqual  ->
               let uu____6634 =
                 let uu____6639 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                   uu____6639
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6634)

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
          (let uu____6711 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6711) &&
            (let uu____6714 =
               FStar_List.existsML
                 (fun uu____6727  ->
                    match uu____6727 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6749)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6754 -> false
                          | uu____6756 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6714)
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
            let uu____6824 = may_drop_implicits args  in
            if uu____6824 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6849  ->
                 match uu____6849 with
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
              ((let uu____6904 =
                  let uu____6906 =
                    let uu____6908 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6908  in
                  Prims.op_Negation uu____6906  in
                if uu____6904
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
              let uu____6952 = filter_pattern_imp args  in
              (match uu____6952 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7002 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7002 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7021 =
                       let uu____7027 =
                         let uu____7029 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7029
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7027)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7021);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7082  ->
                        match uu____7082 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7099 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7099)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7107;
                 FStar_Syntax_Syntax.fv_delta = uu____7108;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7137 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7137 FStar_List.rev  in
              let args1 =
                let uu____7153 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7173  ->
                          match uu____7173 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7153 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7251 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7251
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7274 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7274
                 in
              let args2 =
                let uu____7292 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7292 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7336 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7336 with
               | FStar_Pervasives_Native.Some (op,uu____7348) ->
                   let uu____7365 =
                     let uu____7366 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7366  in
                   mk1 uu____7365
               | FStar_Pervasives_Native.None  ->
                   let uu____7376 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7376 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7381 ->
              let uu____7382 =
                let uu____7383 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7383  in
              mk1 uu____7382
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
          let uu____7423 =
            let uu____7426 =
              let uu____7427 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7427  in
            FStar_Pervasives_Native.Some uu____7426  in
          FStar_Pervasives_Native.Some uu____7423

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
          let uu____7439 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7439

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___205_7447  ->
    match uu___205_7447 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7454 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7455 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7456 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7461 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7470 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7479 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___206_7485  ->
    match uu___206_7485 with
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
            (tylid,uvs,bs,t,uu____7528,datacons) ->
            let uu____7538 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7566,uu____7567,uu____7568,inductive_lid,uu____7570,uu____7571)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7578 -> failwith "unexpected"))
               in
            (match uu____7538 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7599 = FStar_Options.print_implicits ()  in
                   if uu____7599 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7616 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___207_7623  ->
                             match uu___207_7623 with
                             | FStar_Syntax_Syntax.RecordType uu____7625 ->
                                 true
                             | uu____7635 -> false))
                      in
                   if uu____7616
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7689,univs1,term,uu____7692,num,uu____7694)
                           ->
                           let uu____7701 =
                             let uu____7702 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7702.FStar_Syntax_Syntax.n  in
                           (match uu____7701 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7716)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7785  ->
                                          match uu____7785 with
                                          | (b,qual) ->
                                              let uu____7806 =
                                                bv_as_unique_ident b  in
                                              let uu____7807 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____7806, uu____7807,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____7818 -> failwith "unexpected")
                       | uu____7830 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____7961,num,uu____7963) ->
                            let c =
                              let uu____7984 =
                                let uu____7987 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____7987  in
                              ((l.FStar_Ident.ident), uu____7984,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____8007 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8087 ->
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
        let uu____8113 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8113;
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
        let uu____8143 = ts  in
        match uu____8143 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8156 =
              let uu____8157 =
                let uu____8174 =
                  let uu____8183 =
                    let uu____8190 =
                      let uu____8191 =
                        let uu____8204 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8204)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8191  in
                    (uu____8190, FStar_Pervasives_Native.None)  in
                  [uu____8183]  in
                (false, false, uu____8174)  in
              FStar_Parser_AST.Tycon uu____8157  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8156
  
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
              let uu____8293 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____8293 with
              | (bs,action_defn) ->
                  let uu____8300 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____8300 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____8310 = FStar_Options.print_implicits ()
                            in
                         if uu____8310
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____8320 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____8320 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____8337 =
                             let uu____8348 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____8348,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____8337  in
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
            let uu____8432 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____8432 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____8442 = FStar_Options.print_implicits ()  in
                  if uu____8442 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____8452 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____8452 FStar_List.rev  in
                let eff_typ1 = resugar_term' env eff_typ  in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8537) ->
          let uu____8546 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8569 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8587 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8595 -> false
                    | uu____8612 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8546 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8650 se1 =
                 match uu____8650 with
                 | (datacon_ses1,tycons) ->
                     let uu____8676 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8676 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8691 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8691 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8726 =
                           let uu____8727 =
                             let uu____8728 =
                               let uu____8745 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____8745)  in
                             FStar_Parser_AST.Tycon uu____8728  in
                           decl'_to_decl se uu____8727  in
                         FStar_Pervasives_Native.Some uu____8726
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8780,uu____8781,uu____8782,uu____8783,uu____8784)
                              ->
                              let uu____8791 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8791
                          | uu____8794 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8798 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8805) ->
          let uu____8810 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___208_8818  ->
                    match uu___208_8818 with
                    | FStar_Syntax_Syntax.Projector (uu____8820,uu____8821)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8823 -> true
                    | uu____8825 -> false))
             in
          if uu____8810
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
             | FStar_Parser_AST.Let (isrec,lets,uu____8860) ->
                 let uu____8889 =
                   let uu____8890 =
                     let uu____8891 =
                       let uu____8902 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____8902)  in
                     FStar_Parser_AST.TopLevelLet uu____8891  in
                   decl'_to_decl se uu____8890  in
                 FStar_Pervasives_Native.Some uu____8889
             | uu____8939 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____8944,fml) ->
          let uu____8946 =
            let uu____8947 =
              let uu____8948 =
                let uu____8953 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____8953)  in
              FStar_Parser_AST.Assume uu____8948  in
            decl'_to_decl se uu____8947  in
          FStar_Pervasives_Native.Some uu____8946
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____8955 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8955
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____8958 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8958
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____8968,t) ->
                let uu____8978 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8978
            | uu____8979 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____8987,t) ->
                let uu____8997 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8997
            | uu____8998 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9022 -> failwith "Should not happen hopefully"  in
          let uu____9032 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9032
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____9042 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9042 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9054 = FStar_Options.print_implicits ()  in
                 if uu____9054 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9070 =
                 let uu____9071 =
                   let uu____9072 =
                     let uu____9089 =
                       let uu____9098 =
                         let uu____9105 =
                           let uu____9106 =
                             let uu____9119 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9119)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9106  in
                         (uu____9105, FStar_Pervasives_Native.None)  in
                       [uu____9098]  in
                     (false, false, uu____9089)  in
                   FStar_Parser_AST.Tycon uu____9072  in
                 decl'_to_decl se uu____9071  in
               FStar_Pervasives_Native.Some uu____9070)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9151 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9151
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9155 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___209_9163  ->
                    match uu___209_9163 with
                    | FStar_Syntax_Syntax.Projector (uu____9165,uu____9166)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9168 -> true
                    | uu____9170 -> false))
             in
          if uu____9155
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9178 =
                 (let uu____9182 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9182) || (FStar_List.isEmpty uvs)
                  in
               if uu____9178
               then resugar_term' env t
               else
                 (let uu____9187 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9187 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9196 = resugar_term' env t1  in
                      label universes uu____9196)
                in
             let uu____9197 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9197)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9204 =
            let uu____9205 =
              let uu____9206 =
                let uu____9213 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9218 = resugar_term' env t  in
                (uu____9213, uu____9218)  in
              FStar_Parser_AST.Splice uu____9206  in
            decl'_to_decl se uu____9205  in
          FStar_Pervasives_Native.Some uu____9204
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9221 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9238 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9254 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9278 = noenv resugar_term'  in uu____9278 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9296 = noenv resugar_sigelt'  in uu____9296 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9314 = noenv resugar_comp'  in uu____9314 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9337 = noenv resugar_pat'  in uu____9337 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9371 = noenv resugar_binder'  in uu____9371 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9396 = noenv resugar_tscheme'  in uu____9396 ts 
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
          let uu____9431 = noenv resugar_eff_decl'  in
          uu____9431 for_free r q ed
  