open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.of_int (100)) doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____15 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____15
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____23 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____23
  
let map_opt :
  'Auu____31 'Auu____32 .
    unit ->
      ('Auu____31 -> 'Auu____32 FStar_Pervasives_Native.option) ->
        'Auu____31 Prims.list -> 'Auu____32 Prims.list
  = fun uu____48  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____57 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____57
      then
        let uu____61 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____61
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____71 .
    ('Auu____71 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____71 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_126  ->
            match uu___0_126 with
            | (uu____134,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____141,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____142)) -> false
            | (uu____147,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____148)) -> false
            | uu____154 -> true))
  
let filter_pattern_imp :
  'Auu____167 .
    ('Auu____167 * Prims.bool) Prims.list ->
      ('Auu____167 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____202  ->
         match uu____202 with
         | (uu____209,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____259 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____272 = FStar_Options.print_universes ()  in
    if uu____272
    then
      let uu____276 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____276 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____340 ->
          let uu____341 = universe_to_int Prims.int_zero u  in
          (match uu____341 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____352 =
                      let uu____353 =
                        let uu____354 =
                          let uu____366 = FStar_Util.string_of_int n1  in
                          (uu____366, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____354  in
                      FStar_Parser_AST.Const uu____353  in
                    mk1 uu____352 r
                | uu____379 ->
                    let e1 =
                      let uu____381 =
                        let uu____382 =
                          let uu____383 =
                            let uu____395 = FStar_Util.string_of_int n1  in
                            (uu____395, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____383  in
                        FStar_Parser_AST.Const uu____382  in
                      mk1 uu____381 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____409 =
                      let uu____410 =
                        let uu____417 = FStar_Ident.id_of_text "+"  in
                        (uu____417, [e1; e2])  in
                      FStar_Parser_AST.Op uu____410  in
                    mk1 uu____409 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____425 ->
               let t =
                 let uu____429 =
                   let uu____430 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____430  in
                 mk1 uu____429 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____439 =
                        let uu____440 =
                          let uu____447 = resugar_universe x r  in
                          (acc, uu____447, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____440  in
                      mk1 uu____439 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____449 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____461 =
              let uu____467 =
                let uu____469 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____469  in
              (uu____467, r)  in
            FStar_Ident.mk_ident uu____461  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___1_507 =
      match uu___1_507 with
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
      | uu____835 -> FStar_Pervasives_Native.None  in
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
    | uu____975 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____993 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____993 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1011 ->
               let op =
                 let uu____1017 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____1071) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____1017
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
      let uu____1398 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1398 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1468 ->
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
                (let uu____1570 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1570
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1606 =
      let uu____1607 = FStar_Syntax_Subst.compress t  in
      uu____1607.FStar_Syntax_Syntax.n  in
    match uu____1606 with
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
        let uu____1628 = string_to_op s  in
        (match uu____1628 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1668 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1685 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1702 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1713 -> true
    | uu____1715 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1736 ->
        let uu____1738 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1738
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1752 = may_shorten lid  in
      if uu____1752 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1897 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1897  in
      let uu____1900 =
        let uu____1901 = FStar_Syntax_Subst.compress t  in
        uu____1901.FStar_Syntax_Syntax.n  in
      match uu____1900 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1904 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1929 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1929
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1932 =
              let uu____1935 = bv_as_unique_ident x  in [uu____1935]  in
            FStar_Ident.lid_of_ids uu____1932  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1938 =
              let uu____1941 = bv_as_unique_ident x  in [uu____1941]  in
            FStar_Ident.lid_of_ids uu____1938  in
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
            let uu____1960 =
              let uu____1961 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1961  in
            mk1 uu____1960
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
               | uu____1985 -> failwith "wrong projector format")
            else
              (let uu____1992 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1996 =
                      let uu____1998 = FStar_String.get s Prims.int_zero  in
                      FStar_Char.uppercase uu____1998  in
                    let uu____2001 = FStar_String.get s Prims.int_zero  in
                    uu____1996 <> uu____2001)
                  in
               if uu____1992
               then
                 let uu____2006 =
                   let uu____2007 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____2007  in
                 mk1 uu____2006
               else
                 (let uu____2010 =
                    let uu____2011 =
                      let uu____2022 = maybe_shorten_fv env fv  in
                      (uu____2022, [])  in
                    FStar_Parser_AST.Construct uu____2011  in
                  mk1 uu____2010))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2040 = FStar_Options.print_universes ()  in
          if uu____2040
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
                   let uu____2071 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2071  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2094 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2102 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2102
          then
            let uu____2105 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2105
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2110 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2131 -> ("Type", true)  in
          (match uu____2110 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2143 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2143  in
               let uu____2144 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2144
               then
                 let uu____2147 =
                   let uu____2148 =
                     let uu____2155 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2155, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2148  in
                 mk1 uu____2147
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2160) ->
          let uu____2185 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2185 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2201 = FStar_Options.print_implicits ()  in
                 if uu____2201 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2239  ->
                         match uu____2239 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2279 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2279 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2289 = FStar_Options.print_implicits ()  in
                 if uu____2289 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2300 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2300 FStar_List.rev  in
               let rec aux body3 uu___2_2325 =
                 match uu___2_2325 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2341 =
            let uu____2346 =
              let uu____2347 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2347]  in
            FStar_Syntax_Subst.open_term uu____2346 phi  in
          (match uu____2341 with
           | (x1,phi1) ->
               let b =
                 let uu____2369 =
                   let uu____2372 = FStar_List.hd x1  in
                   resugar_binder' env uu____2372 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2369  in
               let uu____2379 =
                 let uu____2380 =
                   let uu____2385 = resugar_term' env phi1  in
                   (b, uu____2385)  in
                 FStar_Parser_AST.Refine uu____2380  in
               mk1 uu____2379)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2387;
             FStar_Syntax_Syntax.vars = uu____2388;_},(e,uu____2390)::[])
          when
          (let uu____2431 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2431) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2480 =
            match uu___3_2480 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2550 -> failwith "last of an empty list"  in
          let rec last_two uu___4_2589 =
            match uu___4_2589 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____2621::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2699::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2770  ->
                   match uu____2770 with
                   | (e2,qual) ->
                       let uu____2787 = resugar_term' env e2  in
                       let uu____2788 = resugar_imp env qual  in
                       (uu____2787, uu____2788)) args1
               in
            let uu____2789 = resugar_term' env e1  in
            match uu____2789 with
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
                     fun uu____2826  ->
                       match uu____2826 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2842 = FStar_Options.print_implicits ()  in
            if uu____2842 then args else filter_imp args  in
          let uu____2857 = resugar_term_as_op e  in
          (match uu____2857 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2870) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2895  ->
                        match uu____2895 with
                        | (x,uu____2907) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2916 =
                                   let uu____2917 =
                                     let uu____2918 =
                                       let uu____2925 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2925, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2918  in
                                   mk1 uu____2917  in
                                 FStar_Pervasives_Native.Some uu____2916))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2929) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2955)::[] -> b
                 | uu____2972 -> failwith "wrong arguments to dtuple"  in
               let uu____2982 =
                 let uu____2983 = FStar_Syntax_Subst.compress body  in
                 uu____2983.FStar_Syntax_Syntax.n  in
               (match uu____2982 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2988) ->
                    let uu____3013 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3013 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3023 = FStar_Options.print_implicits ()
                              in
                           if uu____3023 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3040 =
                           let uu____3041 =
                             let uu____3052 =
                               FStar_List.map
                                 (fun _3063  -> FStar_Util.Inl _3063) xs3
                                in
                             (uu____3052, body3)  in
                           FStar_Parser_AST.Sum uu____3041  in
                         mk1 uu____3040)
                | uu____3070 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3093  ->
                              match uu____3093 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3111) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3120) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3129 = FStar_List.hd args1  in
               (match uu____3129 with
                | (t1,uu____3143) ->
                    let uu____3148 =
                      let uu____3149 = FStar_Syntax_Subst.compress t1  in
                      uu____3149.FStar_Syntax_Syntax.n  in
                    (match uu____3148 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3156 =
                           let uu____3157 =
                             let uu____3162 = resugar_term' env t1  in
                             (uu____3162, f)  in
                           FStar_Parser_AST.Project uu____3157  in
                         mk1 uu____3156
                     | uu____3163 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3164) when
               (FStar_List.length args1) > Prims.int_one ->
               let new_args = last_two args1  in
               let uu____3188 =
                 match new_args with
                 | (a1,uu____3198)::(a2,uu____3200)::[] -> (a1, a2)
                 | uu____3227 -> failwith "wrong arguments to try_with"  in
               (match uu____3188 with
                | (body,handler) ->
                    let decomp term =
                      let uu____3249 =
                        let uu____3250 = FStar_Syntax_Subst.compress term  in
                        uu____3250.FStar_Syntax_Syntax.n  in
                      match uu____3249 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____3255) ->
                          let uu____3280 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____3280 with | (x1,e2) -> e2)
                      | uu____3287 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____3290 = decomp body  in
                      resugar_term' env uu____3290  in
                    let handler1 =
                      let uu____3292 = decomp handler  in
                      resugar_term' env uu____3292  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____3300,uu____3301,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____3333,uu____3334,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____3371 =
                            let uu____3372 =
                              let uu____3381 = resugar_body t11  in
                              (uu____3381, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____3372  in
                          mk1 uu____3371
                      | uu____3384 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____3442 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____3472) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3481) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3502) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,(uu____3567,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,(uu____3599,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3630 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3643 =
                   let uu____3644 = FStar_Syntax_Subst.compress body  in
                   uu____3644.FStar_Syntax_Syntax.n  in
                 match uu____3643 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3649) ->
                     let uu____3674 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3674 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3684 = FStar_Options.print_implicits ()
                               in
                            if uu____3684 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3700 =
                            let uu____3709 =
                              let uu____3710 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3710.FStar_Syntax_Syntax.n  in
                            match uu____3709 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3728 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3745,pats) ->
                                      let uu____3779 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3823  ->
                                                     match uu____3823 with
                                                     | (e2,uu____3831) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3779, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3847 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3847)
                                  | uu____3856 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3728 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3888 ->
                                let uu____3889 = resugar_term' env body2  in
                                ([], uu____3889)
                             in
                          (match uu____3700 with
                           | (pats,body3) ->
                               let uu____3906 = uncurry xs3 pats body3  in
                               (match uu____3906 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      let uu____3944 =
                                        let uu____3945 =
                                          let uu____3964 =
                                            let uu____3975 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs5 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____3975, pats1)  in
                                          (xs5, uu____3964, body4)  in
                                        FStar_Parser_AST.QForall uu____3945
                                         in
                                      mk1 uu____3944
                                    else
                                      (let uu____3998 =
                                         let uu____3999 =
                                           let uu____4018 =
                                             let uu____4029 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs5
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4029, pats1)  in
                                           (xs5, uu____4018, body4)  in
                                         FStar_Parser_AST.QExists uu____3999
                                          in
                                       mk1 uu____3998))))
                 | uu____4050 ->
                     if op = "forall"
                     then
                       let uu____4054 =
                         let uu____4055 =
                           let uu____4074 = resugar_term' env body  in
                           ([], ([], []), uu____4074)  in
                         FStar_Parser_AST.QForall uu____4055  in
                       mk1 uu____4054
                     else
                       (let uu____4097 =
                          let uu____4098 =
                            let uu____4117 = resugar_term' env body  in
                            ([], ([], []), uu____4117)  in
                          FStar_Parser_AST.QExists uu____4098  in
                        mk1 uu____4097)
                  in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4156)::[] -> resugar b
                  | uu____4173 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4185) ->
               let uu____4193 = FStar_List.hd args1  in
               (match uu____4193 with
                | (e1,uu____4207) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4279  ->
                         match uu____4279 with
                         | (e1,qual) ->
                             let uu____4296 = resugar_term' env e1  in
                             let uu____4297 = resugar_imp env qual  in
                             (uu____4296, uu____4297)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4313 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4313 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4361 =
                               let uu____4362 =
                                 let uu____4369 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4369)  in
                               FStar_Parser_AST.Op uu____4362  in
                             mk1 uu____4361  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4387  ->
                                  match uu____4387 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4406 =
                      let uu____4407 =
                        let uu____4414 =
                          let uu____4417 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4417
                           in
                        (op1, uu____4414)  in
                      FStar_Parser_AST.Op uu____4407  in
                    mk1 uu____4406
                | uu____4430 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4499 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4499 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4545 =
                   let uu____4558 =
                     let uu____4563 = resugar_pat' env pat1 branch_bv  in
                     let uu____4564 = resugar_term' env e  in
                     (uu____4563, uu____4564)  in
                   (FStar_Pervasives_Native.None, uu____4558)  in
                 [uu____4545]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4616,t1)::(pat2,uu____4619,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4715 =
            let uu____4716 =
              let uu____4723 = resugar_term' env e  in
              let uu____4724 = resugar_term' env t1  in
              let uu____4725 = resugar_term' env t2  in
              (uu____4723, uu____4724, uu____4725)  in
            FStar_Parser_AST.If uu____4716  in
          mk1 uu____4715
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4791 =
            match uu____4791 with
            | (pat,wopt,b) ->
                let uu____4833 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4833 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4885 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4885
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4889 =
            let uu____4890 =
              let uu____4905 = resugar_term' env e  in
              let uu____4906 = FStar_List.map resugar_branch branches  in
              (uu____4905, uu____4906)  in
            FStar_Parser_AST.Match uu____4890  in
          mk1 uu____4889
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4952) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5021 =
            let uu____5022 =
              let uu____5031 = resugar_term' env e  in
              (uu____5031, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5022  in
          mk1 uu____5021
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5060 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5060 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5114 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5114
                    in
                 let uu____5121 =
                   let uu____5126 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5126
                    in
                 match uu____5121 with
                 | (univs1,td) ->
                     let uu____5146 =
                       let uu____5153 =
                         let uu____5154 = FStar_Syntax_Subst.compress td  in
                         uu____5154.FStar_Syntax_Syntax.n  in
                       match uu____5153 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5163,(t1,uu____5165)::(d,uu____5167)::[])
                           -> (t1, d)
                       | uu____5224 -> failwith "wrong let binding format"
                        in
                     (match uu____5146 with
                      | (typ,def) ->
                          let uu____5255 =
                            let uu____5271 =
                              let uu____5272 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5272.FStar_Syntax_Syntax.n  in
                            match uu____5271 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5292) ->
                                let uu____5317 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5317 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5348 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5348
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5371 -> ([], def, false)  in
                          (match uu____5255 with
                           | (binders,term,is_pat_app) ->
                               let uu____5426 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5437 =
                                       let uu____5438 =
                                         let uu____5439 =
                                           let uu____5446 =
                                             bv_as_unique_ident bv  in
                                           (uu____5446,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5439
                                          in
                                       mk_pat uu____5438  in
                                     (uu____5437, term)
                                  in
                               (match uu____5426 with
                                | (pat,term1) ->
                                    let uu____5468 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5511  ->
                                                  match uu____5511 with
                                                  | (bv,q) ->
                                                      let uu____5526 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5526
                                                        (fun q1  ->
                                                           let uu____5538 =
                                                             let uu____5539 =
                                                               let uu____5546
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5546,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5539
                                                              in
                                                           mk_pat uu____5538)))
                                           in
                                        let uu____5549 =
                                          let uu____5554 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5554)
                                           in
                                        let uu____5557 =
                                          universe_to_string univs1  in
                                        (uu____5549, uu____5557)
                                      else
                                        (let uu____5566 =
                                           let uu____5571 =
                                             resugar_term' env term1  in
                                           (pat, uu____5571)  in
                                         let uu____5572 =
                                           universe_to_string univs1  in
                                         (uu____5566, uu____5572))
                                       in
                                    (attrs_opt, uu____5468))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5678 =
                   match uu____5678 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5738 =
                         let uu____5740 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5740  in
                       if uu____5738
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5821) ->
          let s =
            let uu____5840 =
              let uu____5842 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5842 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5840  in
          let uu____5847 = mk1 FStar_Parser_AST.Wild  in label s uu____5847
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5855 =
            let uu____5856 =
              let uu____5861 = resugar_term' env tm  in (uu____5861, qi1)  in
            FStar_Parser_AST.Quote uu____5856  in
          mk1 uu____5855
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___5_5873 =
            match uu___5_5873 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5881,(uu____5882,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____5943 =
                        let uu____5944 =
                          let uu____5953 = resugar_seq t11  in
                          (uu____5953, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____5944  in
                      mk1 uu____5943
                  | uu____5956 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____5957,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6021  ->
                         match uu____6021 with
                         | (x,uu____6029) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6034 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____6052,t1) ->
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
               let uu____6092 = FStar_Options.print_universes ()  in
               if uu____6092
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
               let uu____6156 = FStar_Options.print_universes ()  in
               if uu____6156
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
            let uu____6200 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6200, FStar_Parser_AST.Nothing)  in
          let uu____6201 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6201
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6224 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6224
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6309 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6309, (FStar_Pervasives_Native.snd post))  in
                    let uu____6320 =
                      let uu____6329 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6329 then [] else [pre]  in
                    let uu____6364 =
                      let uu____6373 =
                        let uu____6382 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6382 then [] else [pats]  in
                      FStar_List.append [post1] uu____6373  in
                    FStar_List.append uu____6320 uu____6364
                | uu____6441 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6475  ->
                   match uu____6475 with
                   | (e,uu____6487) ->
                       let uu____6492 = resugar_term' env e  in
                       (uu____6492, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___6_6517 =
              match uu___6_6517 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6550 = resugar_term' env e  in
                         (uu____6550, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6555 -> aux l tl1)
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
        let uu____6602 = b  in
        match uu____6602 with
        | (x,aq) ->
            let uu____6611 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6611
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6625 =
                       let uu____6626 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6626  in
                     FStar_Parser_AST.mk_binder uu____6625 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6627 ->
                     let uu____6628 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6628
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6633 =
                          let uu____6634 =
                            let uu____6639 = bv_as_unique_ident x  in
                            (uu____6639, e)  in
                          FStar_Parser_AST.Annotated uu____6634  in
                        FStar_Parser_AST.mk_binder uu____6633 r
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
              let uu____6659 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6659  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6663 =
                if used
                then
                  let uu____6665 =
                    let uu____6672 = bv_as_unique_ident v1  in
                    (uu____6672, aqual)  in
                  FStar_Parser_AST.PatVar uu____6665
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6663  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6679;
                  FStar_Syntax_Syntax.vars = uu____6680;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6690 = FStar_Options.print_bound_var_types ()  in
                if uu____6690
                then
                  let uu____6693 =
                    let uu____6694 =
                      let uu____6705 =
                        let uu____6712 = resugar_term' env typ  in
                        (uu____6712, FStar_Pervasives_Native.None)  in
                      (pat, uu____6705)  in
                    FStar_Parser_AST.PatAscribed uu____6694  in
                  mk1 uu____6693
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
          let uu____6733 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6733
            (fun aqual  ->
               let uu____6745 =
                 let uu____6750 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6761  -> FStar_Pervasives_Native.Some _6761)
                   uu____6750
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6745)

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
          (let uu____6823 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6823) &&
            (let uu____6826 =
               FStar_List.existsML
                 (fun uu____6839  ->
                    match uu____6839 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6861)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6866 -> false
                          | uu____6868 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6826)
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
            let uu____6936 = may_drop_implicits args  in
            if uu____6936 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6961  ->
                 match uu____6961 with
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
              ((let uu____7016 =
                  let uu____7018 =
                    let uu____7020 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7020  in
                  Prims.op_Negation uu____7018  in
                if uu____7016
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
              let uu____7064 = filter_pattern_imp args  in
              (match uu____7064 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7114 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7114 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7133 =
                       let uu____7139 =
                         let uu____7141 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7141
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7139)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7133);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7194  ->
                        match uu____7194 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7211 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7211)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7219;
                 FStar_Syntax_Syntax.fv_delta = uu____7220;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7249 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7249 FStar_List.rev  in
              let args1 =
                let uu____7265 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7285  ->
                          match uu____7285 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7265 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7363 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7363
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7386 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7386
                 in
              let args2 =
                let uu____7404 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7404 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7448 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7448 with
               | FStar_Pervasives_Native.Some (op,uu____7460) ->
                   let uu____7477 =
                     let uu____7478 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7478  in
                   mk1 uu____7477
               | FStar_Pervasives_Native.None  ->
                   let uu____7488 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7488 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7493 ->
              let uu____7494 =
                let uu____7495 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7495  in
              mk1 uu____7494
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
          let uu____7535 =
            let uu____7538 =
              let uu____7539 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7539  in
            FStar_Pervasives_Native.Some uu____7538  in
          FStar_Pervasives_Native.Some uu____7535

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
          let uu____7551 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7551

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___7_7559  ->
    match uu___7_7559 with
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
    | FStar_Syntax_Syntax.Reflectable uu____7566 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7567 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7568 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7573 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7582 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7591 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___8_7597  ->
    match uu___8_7597 with
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
            (tylid,uvs,bs,t,uu____7640,datacons) ->
            let uu____7650 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7678,uu____7679,uu____7680,inductive_lid,uu____7682,uu____7683)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7690 -> failwith "unexpected"))
               in
            (match uu____7650 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7711 = FStar_Options.print_implicits ()  in
                   if uu____7711 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7728 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___9_7735  ->
                             match uu___9_7735 with
                             | FStar_Syntax_Syntax.RecordType uu____7737 ->
                                 true
                             | uu____7747 -> false))
                      in
                   if uu____7728
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7801,univs1,term,uu____7804,num,uu____7806)
                           ->
                           let uu____7813 =
                             let uu____7814 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7814.FStar_Syntax_Syntax.n  in
                           (match uu____7813 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7828)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7897  ->
                                          match uu____7897 with
                                          | (b,qual) ->
                                              let uu____7918 =
                                                bv_as_unique_ident b  in
                                              let uu____7919 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____7918, uu____7919,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____7930 -> failwith "unexpected")
                       | uu____7942 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____8073,num,uu____8075) ->
                            let c =
                              let uu____8096 =
                                let uu____8099 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8099  in
                              ((l.FStar_Ident.ident), uu____8096,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____8119 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8199 ->
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
        let uu____8225 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8225;
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
        let uu____8255 = ts  in
        match uu____8255 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8268 =
              let uu____8269 =
                let uu____8286 =
                  let uu____8295 =
                    let uu____8302 =
                      let uu____8303 =
                        let uu____8316 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8316)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8303  in
                    (uu____8302, FStar_Pervasives_Native.None)  in
                  [uu____8295]  in
                (false, false, uu____8286)  in
              FStar_Parser_AST.Tycon uu____8269  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8268
  
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
              let uu____8405 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____8405 with
              | (bs,action_defn) ->
                  let uu____8412 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____8412 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____8422 = FStar_Options.print_implicits ()
                            in
                         if uu____8422
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____8432 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____8432 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____8449 =
                             let uu____8460 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____8460,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____8449  in
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
            let uu____8544 =
              let uu____8549 =
                FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                  FStar_Pervasives_Native.snd
                 in
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                uu____8549
               in
            match uu____8544 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____8563 = FStar_Options.print_implicits ()  in
                  if uu____8563 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____8573 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____8573 FStar_List.rev  in
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
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial
                   in
                let repr =
                  resugar_tscheme'' env "repr" ed.FStar_Syntax_Syntax.repr
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8648) ->
          let uu____8657 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8680 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8698 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8706 -> false
                    | uu____8723 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8657 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8761 se1 =
                 match uu____8761 with
                 | (datacon_ses1,tycons) ->
                     let uu____8787 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8787 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8802 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8802 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8837 =
                           let uu____8838 =
                             let uu____8839 =
                               let uu____8856 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____8856)  in
                             FStar_Parser_AST.Tycon uu____8839  in
                           decl'_to_decl se uu____8838  in
                         FStar_Pervasives_Native.Some uu____8837
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8891,uu____8892,uu____8893,uu____8894,uu____8895)
                              ->
                              let uu____8902 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8902
                          | uu____8905 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8909 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____8916) ->
          let uu____8921 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_8929  ->
                    match uu___10_8929 with
                    | FStar_Syntax_Syntax.Projector (uu____8931,uu____8932)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8934 -> true
                    | uu____8936 -> false))
             in
          if uu____8921
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
             | FStar_Parser_AST.Let (isrec,lets,uu____8971) ->
                 let uu____9000 =
                   let uu____9001 =
                     let uu____9002 =
                       let uu____9013 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9013)  in
                     FStar_Parser_AST.TopLevelLet uu____9002  in
                   decl'_to_decl se uu____9001  in
                 FStar_Pervasives_Native.Some uu____9000
             | uu____9050 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9055,fml) ->
          let uu____9057 =
            let uu____9058 =
              let uu____9059 =
                let uu____9064 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9064)  in
              FStar_Parser_AST.Assume uu____9059  in
            decl'_to_decl se uu____9058  in
          FStar_Pervasives_Native.Some uu____9057
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9066 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9066
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____9069 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9069
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9079,t) ->
                let uu____9089 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9089
            | uu____9090 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9098,t) ->
                let uu____9108 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9108
            | uu____9109 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9133 -> failwith "Should not happen hopefully"  in
          let uu____9143 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9143
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9153 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9153 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9165 = FStar_Options.print_implicits ()  in
                 if uu____9165 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9181 =
                 let uu____9182 =
                   let uu____9183 =
                     let uu____9200 =
                       let uu____9209 =
                         let uu____9216 =
                           let uu____9217 =
                             let uu____9230 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9230)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9217  in
                         (uu____9216, FStar_Pervasives_Native.None)  in
                       [uu____9209]  in
                     (false, false, uu____9200)  in
                   FStar_Parser_AST.Tycon uu____9183  in
                 decl'_to_decl se uu____9182  in
               FStar_Pervasives_Native.Some uu____9181)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9262 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9262
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9266 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___11_9274  ->
                    match uu___11_9274 with
                    | FStar_Syntax_Syntax.Projector (uu____9276,uu____9277)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9279 -> true
                    | uu____9281 -> false))
             in
          if uu____9266
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9289 =
                 (let uu____9293 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9293) || (FStar_List.isEmpty uvs)
                  in
               if uu____9289
               then resugar_term' env t
               else
                 (let uu____9298 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9298 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9307 = resugar_term' env t1  in
                      label universes uu____9307)
                in
             let uu____9308 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9308)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9315 =
            let uu____9316 =
              let uu____9317 =
                let uu____9324 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9329 = resugar_term' env t  in
                (uu____9324, uu____9329)  in
              FStar_Parser_AST.Splice uu____9317  in
            decl'_to_decl se uu____9316  in
          FStar_Pervasives_Native.Some uu____9315
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9332 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9349 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9365 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9389 = noenv resugar_term'  in uu____9389 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9407 = noenv resugar_sigelt'  in uu____9407 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9425 = noenv resugar_comp'  in uu____9425 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9448 = noenv resugar_pat'  in uu____9448 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9482 = noenv resugar_binder'  in uu____9482 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9507 = noenv resugar_tscheme'  in uu____9507 ts 
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
          let uu____9542 = noenv resugar_eff_decl'  in
          uu____9542 for_free r q ed
  