open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____11 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____11
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____17 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____17
  
let map_opt :
  'Auu____26 'Auu____27 .
    unit ->
      ('Auu____26 -> 'Auu____27 FStar_Pervasives_Native.option) ->
        'Auu____26 Prims.list -> 'Auu____27 Prims.list
  = fun uu____43  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____50 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____50
      then
        let uu____51 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____51
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____57 .
    ('Auu____57,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____57,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___67_112  ->
            match uu___67_112 with
            | (uu____119,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____120)) -> false
            | uu____123 -> true))
  
let filter_pattern_imp :
  'Auu____134 .
    ('Auu____134,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____134,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____165  ->
         match uu____165 with
         | (uu____170,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
  
let (resugar_arg_qual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  =
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
  
let (resugar_imp :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.imp)
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        FStar_Parser_AST.Hash
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        FStar_Parser_AST.Nothing
  
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____246 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____256 = FStar_Options.print_universes ()  in
    if uu____256
    then
      let uu____257 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____257 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____311 ->
          let uu____312 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____312 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____319 =
                      let uu____320 =
                        let uu____321 =
                          let uu____332 = FStar_Util.string_of_int n1  in
                          (uu____332, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____321  in
                      FStar_Parser_AST.Const uu____320  in
                    mk1 uu____319 r
                | uu____343 ->
                    let e1 =
                      let uu____345 =
                        let uu____346 =
                          let uu____347 =
                            let uu____358 = FStar_Util.string_of_int n1  in
                            (uu____358, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____347  in
                        FStar_Parser_AST.Const uu____346  in
                      mk1 uu____345 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____370 =
                      let uu____371 =
                        let uu____378 = FStar_Ident.id_of_text "+"  in
                        (uu____378, [e1; e2])  in
                      FStar_Parser_AST.Op uu____371  in
                    mk1 uu____370 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____384 ->
               let t =
                 let uu____388 =
                   let uu____389 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____389  in
                 mk1 uu____388 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____395 =
                        let uu____396 =
                          let uu____403 = resugar_universe x r  in
                          (acc, uu____403, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____396  in
                      mk1 uu____395 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____405 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____416 =
              let uu____421 =
                let uu____422 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____422  in
              (uu____421, r)  in
            FStar_Ident.mk_ident uu____416  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string,Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___68_449 =
      match uu___68_449 with
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
      | uu____626 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____673 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____685 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____685 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____695 ->
               let op =
                 let uu____699 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____741) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____699
                  in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
  
type expected_arity = Prims.int FStar_Pervasives_Native.option[@@deriving
                                                                show]
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string,expected_arity) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
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
      let uu____949 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____949 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1003 ->
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
                (let uu____1074 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1074
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1098 =
      let uu____1099 = FStar_Syntax_Subst.compress t  in
      uu____1099.FStar_Syntax_Syntax.n  in
    match uu____1098 with
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
        let uu____1122 = string_to_op s  in
        (match uu____1122 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1154 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1169 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1179 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1185 -> true
    | uu____1186 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1197 ->
        let uu____1198 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1198
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1210 = may_shorten lid  in
      if uu____1210 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1323 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1323  in
      let uu____1324 =
        let uu____1325 = FStar_Syntax_Subst.compress t  in
        uu____1325.FStar_Syntax_Syntax.n  in
      match uu____1324 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1328 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1354 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1354
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1357 =
              let uu____1360 = bv_as_unique_ident x  in [uu____1360]  in
            FStar_Ident.lid_of_ids uu____1357  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1363 =
              let uu____1366 = bv_as_unique_ident x  in [uu____1366]  in
            FStar_Ident.lid_of_ids uu____1363  in
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
            let uu____1384 =
              let uu____1385 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1385  in
            mk1 uu____1384
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
               | uu____1395 -> failwith "wrong projector format")
            else
              (let uu____1399 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1402 =
                      let uu____1404 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1404  in
                    let uu____1406 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1402 <> uu____1406)
                  in
               if uu____1399
               then
                 let uu____1409 =
                   let uu____1410 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1410  in
                 mk1 uu____1409
               else
                 (let uu____1412 =
                    let uu____1413 =
                      let uu____1424 = maybe_shorten_fv env fv  in
                      (uu____1424, [])  in
                    FStar_Parser_AST.Construct uu____1413  in
                  mk1 uu____1412))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1442 = FStar_Options.print_universes ()  in
          if uu____1442
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
                   let uu____1471 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1471  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1494 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1501 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1501
          then
            let uu____1502 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1502
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1505 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1514 -> ("Type", true)  in
          (match uu____1505 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1518 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1518  in
               let uu____1519 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1519
               then
                 let uu____1520 =
                   let uu____1521 =
                     let uu____1528 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1528, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1521  in
                 mk1 uu____1520
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1532) ->
          let uu____1553 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1553 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1567 = FStar_Options.print_implicits ()  in
                 if uu____1567 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1596  ->
                         match uu____1596 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____1626 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1626 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1636 = FStar_Options.print_implicits ()  in
                 if uu____1636 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1644 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1644 FStar_List.rev  in
               let rec aux body3 uu___69_1669 =
                 match uu___69_1669 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1685 =
            let uu____1690 =
              let uu____1691 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1691]  in
            FStar_Syntax_Subst.open_term uu____1690 phi  in
          (match uu____1685 with
           | (x1,phi1) ->
               let b =
                 let uu____1707 =
                   let uu____1710 = FStar_List.hd x1  in
                   resugar_binder' env uu____1710 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1707  in
               let uu____1715 =
                 let uu____1716 =
                   let uu____1721 = resugar_term' env phi1  in
                   (b, uu____1721)  in
                 FStar_Parser_AST.Refine uu____1716  in
               mk1 uu____1715)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1723;
             FStar_Syntax_Syntax.vars = uu____1724;_},(e,uu____1726)::[])
          when
          (let uu____1757 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1757) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___70_1801 =
            match uu___70_1801 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1871 -> failwith "last of an empty list"  in
          let rec last_two uu___71_1909 =
            match uu___71_1909 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1940::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2017::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2088  ->
                   match uu____2088 with
                   | (e2,qual) ->
                       let uu____2105 = resugar_term' env e2  in
                       let uu____2106 = resugar_imp qual  in
                       (uu____2105, uu____2106)) args1
               in
            let uu____2107 = resugar_term' env e1  in
            match uu____2107 with
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
                     fun uu____2144  ->
                       match uu____2144 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2160 = FStar_Options.print_implicits ()  in
            if uu____2160 then args else filter_imp args  in
          let uu____2172 = resugar_term_as_op e  in
          (match uu____2172 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2183) ->
               (match args1 with
                | (fst1,uu____2189)::(snd1,uu____2191)::rest ->
                    let e1 =
                      let uu____2222 =
                        let uu____2223 =
                          let uu____2230 = FStar_Ident.id_of_text "*"  in
                          let uu____2231 =
                            let uu____2234 = resugar_term' env fst1  in
                            let uu____2235 =
                              let uu____2238 = resugar_term' env snd1  in
                              [uu____2238]  in
                            uu____2234 :: uu____2235  in
                          (uu____2230, uu____2231)  in
                        FStar_Parser_AST.Op uu____2223  in
                      mk1 uu____2222  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2253  ->
                           match uu____2253 with
                           | (x,uu____2261) ->
                               let uu____2266 =
                                 let uu____2267 =
                                   let uu____2274 =
                                     FStar_Ident.id_of_text "*"  in
                                   let uu____2275 =
                                     let uu____2278 =
                                       let uu____2281 = resugar_term' env x
                                          in
                                       [uu____2281]  in
                                     e1 :: uu____2278  in
                                   (uu____2274, uu____2275)  in
                                 FStar_Parser_AST.Op uu____2267  in
                               mk1 uu____2266) e1 rest
                | uu____2284 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2293) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2315)::[] -> b
                 | uu____2332 -> failwith "wrong arguments to dtuple"  in
               let uu____2341 =
                 let uu____2342 = FStar_Syntax_Subst.compress body  in
                 uu____2342.FStar_Syntax_Syntax.n  in
               (match uu____2341 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2347) ->
                    let uu____2368 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2368 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2378 = FStar_Options.print_implicits ()
                              in
                           if uu____2378 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2394 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2417  ->
                              match uu____2417 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2435) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2441) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2446 = FStar_List.hd args1  in
               (match uu____2446 with
                | (t1,uu____2460) ->
                    let uu____2465 =
                      let uu____2466 = FStar_Syntax_Subst.compress t1  in
                      uu____2466.FStar_Syntax_Syntax.n  in
                    (match uu____2465 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2471 =
                           let uu____2472 =
                             let uu____2477 = resugar_term' env t1  in
                             (uu____2477, f)  in
                           FStar_Parser_AST.Project uu____2472  in
                         mk1 uu____2471
                     | uu____2478 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2479) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2499 =
                 match new_args with
                 | (a1,uu____2509)::(a2,uu____2511)::[] -> (a1, a2)
                 | uu____2538 -> failwith "wrong arguments to try_with"  in
               (match uu____2499 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2559 =
                        let uu____2560 = FStar_Syntax_Subst.compress term  in
                        uu____2560.FStar_Syntax_Syntax.n  in
                      match uu____2559 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2565) ->
                          let uu____2586 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2586 with | (x1,e2) -> e2)
                      | uu____2593 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2595 = decomp body  in
                      resugar_term' env uu____2595  in
                    let handler1 =
                      let uu____2597 = decomp handler  in
                      resugar_term' env uu____2597  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2605,uu____2606,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2638,uu____2639,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2676 =
                            let uu____2677 =
                              let uu____2686 = resugar_body t11  in
                              (uu____2686, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2677  in
                          mk1 uu____2676
                      | uu____2689 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2746 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2776) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2782) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2873 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2886 =
                   let uu____2887 = FStar_Syntax_Subst.compress body  in
                   uu____2887.FStar_Syntax_Syntax.n  in
                 match uu____2886 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2892) ->
                     let uu____2913 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2913 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2923 = FStar_Options.print_implicits ()
                               in
                            if uu____2923 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2936 =
                            let uu____2945 =
                              let uu____2946 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2946.FStar_Syntax_Syntax.n  in
                            match uu____2945 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____2964 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____2992 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3028  ->
                                                     match uu____3028 with
                                                     | (e2,uu____3034) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____2992, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3042 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3042)
                                  | uu____3049 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____2964 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3080 ->
                                let uu____3081 = resugar_term' env body2  in
                                ([], uu____3081)
                             in
                          (match uu____2936 with
                           | (pats,body3) ->
                               let uu____3098 = uncurry xs3 pats body3  in
                               (match uu____3098 with
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
                 | uu____3146 ->
                     if op = "forall"
                     then
                       let uu____3147 =
                         let uu____3148 =
                           let uu____3161 = resugar_term' env body  in
                           ([], [[]], uu____3161)  in
                         FStar_Parser_AST.QForall uu____3148  in
                       mk1 uu____3147
                     else
                       (let uu____3173 =
                          let uu____3174 =
                            let uu____3187 = resugar_term' env body  in
                            ([], [[]], uu____3187)  in
                          FStar_Parser_AST.QExists uu____3174  in
                        mk1 uu____3173)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3214)::[] -> resugar b
                  | uu____3231 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3241) ->
               let uu____3246 = FStar_List.hd args1  in
               (match uu____3246 with
                | (e1,uu____3260) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3329  ->
                         match uu____3329 with
                         | (e1,qual) ->
                             let uu____3346 = resugar_term' env e1  in
                             let uu____3347 = resugar_imp qual  in
                             (uu____3346, uu____3347)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3360 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3360 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3408 =
                               let uu____3409 =
                                 let uu____3416 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3416)  in
                               FStar_Parser_AST.Op uu____3409  in
                             mk1 uu____3408  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3434  ->
                                  match uu____3434 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3449 =
                      let uu____3450 =
                        let uu____3457 =
                          let uu____3460 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3460
                           in
                        (op1, uu____3457)  in
                      FStar_Parser_AST.Op uu____3450  in
                    mk1 uu____3449
                | uu____3473 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3542 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3542 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3588 =
                   let uu____3601 =
                     let uu____3606 = resugar_pat' env pat1 branch_bv  in
                     let uu____3607 = resugar_term' env e  in
                     (uu____3606, uu____3607)  in
                   (FStar_Pervasives_Native.None, uu____3601)  in
                 [uu____3588]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3659,t1)::(pat2,uu____3662,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3758 =
            let uu____3759 =
              let uu____3766 = resugar_term' env e  in
              let uu____3767 = resugar_term' env t1  in
              let uu____3768 = resugar_term' env t2  in
              (uu____3766, uu____3767, uu____3768)  in
            FStar_Parser_AST.If uu____3759  in
          mk1 uu____3758
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3834 =
            match uu____3834 with
            | (pat,wopt,b) ->
                let uu____3876 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3876 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3928 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3928
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3932 =
            let uu____3933 =
              let uu____3948 = resugar_term' env e  in
              let uu____3949 = FStar_List.map resugar_branch branches  in
              (uu____3948, uu____3949)  in
            FStar_Parser_AST.Match uu____3933  in
          mk1 uu____3932
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3995) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4064 =
            let uu____4065 =
              let uu____4074 = resugar_term' env e  in
              (uu____4074, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4065  in
          mk1 uu____4064
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4100 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4100 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4153 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4153
                    in
                 let uu____4160 =
                   let uu____4165 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4165
                    in
                 match uu____4160 with
                 | (univs1,td) ->
                     let uu____4184 =
                       let uu____4191 =
                         let uu____4192 = FStar_Syntax_Subst.compress td  in
                         uu____4192.FStar_Syntax_Syntax.n  in
                       match uu____4191 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4201,(t1,uu____4203)::(d,uu____4205)::[])
                           -> (t1, d)
                       | uu____4248 -> failwith "wrong let binding format"
                        in
                     (match uu____4184 with
                      | (typ,def) ->
                          let uu____4277 =
                            let uu____4292 =
                              let uu____4293 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4293.FStar_Syntax_Syntax.n  in
                            match uu____4292 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4312) ->
                                let uu____4333 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4333 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4355 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4355
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4357 -> ([], def, false)  in
                          (match uu____4277 with
                           | (binders,term,is_pat_app) ->
                               let uu____4407 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4418 =
                                       let uu____4419 =
                                         let uu____4420 =
                                           let uu____4427 =
                                             bv_as_unique_ident bv  in
                                           (uu____4427,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4420
                                          in
                                       mk_pat uu____4419  in
                                     (uu____4418, term)
                                  in
                               (match uu____4407 with
                                | (pat,term1) ->
                                    let uu____4448 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4488  ->
                                                  match uu____4488 with
                                                  | (bv,q) ->
                                                      let uu____4503 =
                                                        resugar_arg_qual q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4503
                                                        (fun q1  ->
                                                           let uu____4515 =
                                                             let uu____4516 =
                                                               let uu____4523
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4523,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4516
                                                              in
                                                           mk_pat uu____4515)))
                                           in
                                        let uu____4526 =
                                          let uu____4531 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4531)
                                           in
                                        let uu____4534 =
                                          universe_to_string univs1  in
                                        (uu____4526, uu____4534)
                                      else
                                        (let uu____4540 =
                                           let uu____4545 =
                                             resugar_term' env term1  in
                                           (pat, uu____4545)  in
                                         let uu____4546 =
                                           universe_to_string univs1  in
                                         (uu____4540, uu____4546))
                                       in
                                    (attrs_opt, uu____4448))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4646 =
                   match uu____4646 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4702 =
                         let uu____4703 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4703  in
                       if uu____4702
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
      | FStar_Syntax_Syntax.Tm_uvar u ->
          let s =
            let uu____4779 =
              let uu____4780 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____4780 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4779  in
          let uu____4781 = mk1 FStar_Parser_AST.Wild  in label s uu____4781
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____4789 =
            let uu____4790 =
              let uu____4795 = resugar_term' env tm  in (uu____4795, qi1)  in
            FStar_Parser_AST.Quote uu____4790  in
          mk1 uu____4789
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___72_4807 =
            match uu___72_4807 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4815,(uu____4816,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____4877 =
                        let uu____4878 =
                          let uu____4887 = resugar_seq t11  in
                          (uu____4887, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____4878  in
                      mk1 uu____4877
                  | uu____4890 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e
            | FStar_Syntax_Syntax.Mutable_alloc  ->
                let term = resugar_term' env e  in
                (match term.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Let
                     (FStar_Parser_AST.NoLetQualifier ,l,t1) ->
                     mk1
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.Mutable, l, t1))
                 | uu____4936 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval  ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                let uu____4938 =
                  let uu____4939 = FStar_Syntax_Subst.compress e  in
                  uu____4939.FStar_Syntax_Syntax.n  in
                (match uu____4938 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____4943;
                        FStar_Syntax_Syntax.vars = uu____4944;_},(term,uu____4946)::[])
                     -> resugar_term' env term
                 | uu____4975 -> failwith "mutable_rval should have app term")
             in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5011  ->
                         match uu____5011 with
                         | (x,uu____5017) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l,uu____5019,p) ->
               let uu____5021 =
                 let uu____5022 =
                   let uu____5029 = resugar_term' env e  in
                   (uu____5029, l, p)  in
                 FStar_Parser_AST.Labeled uu____5022  in
               mk1 uu____5021
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____5038 =
                 let uu____5039 =
                   let uu____5048 = resugar_term' env e  in
                   let uu____5049 =
                     let uu____5050 =
                       let uu____5051 =
                         let uu____5062 =
                           let uu____5069 =
                             let uu____5074 = resugar_term' env t1  in
                             (uu____5074, FStar_Parser_AST.Nothing)  in
                           [uu____5069]  in
                         (name1, uu____5062)  in
                       FStar_Parser_AST.Construct uu____5051  in
                     mk1 uu____5050  in
                   (uu____5048, uu____5049, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5039  in
               mk1 uu____5038
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5092,t1) ->
               let uu____5098 =
                 let uu____5099 =
                   let uu____5108 = resugar_term' env e  in
                   let uu____5109 =
                     let uu____5110 =
                       let uu____5111 =
                         let uu____5122 =
                           let uu____5129 =
                             let uu____5134 = resugar_term' env t1  in
                             (uu____5134, FStar_Parser_AST.Nothing)  in
                           [uu____5129]  in
                         (name1, uu____5122)  in
                       FStar_Parser_AST.Construct uu____5111  in
                     mk1 uu____5110  in
                   (uu____5108, uu____5109, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5099  in
               mk1 uu____5098)
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
               let uu____5185 = FStar_Options.print_universes ()  in
               if uu____5185
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
               let uu____5246 = FStar_Options.print_universes ()  in
               if uu____5246
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
            let uu____5287 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5287, FStar_Parser_AST.Nothing)  in
          let uu____5288 = FStar_Options.print_effect_args ()  in
          if uu____5288
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____5307 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____5307
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5372 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5372, (FStar_Pervasives_Native.snd post))  in
                    let uu____5381 =
                      let uu____5390 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5390 then [] else [pre]  in
                    let uu____5420 =
                      let uu____5429 =
                        let uu____5438 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5438 then [] else [pats]  in
                      FStar_List.append [post1] uu____5429  in
                    FStar_List.append uu____5381 uu____5420
                | uu____5492 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5521  ->
                   match uu____5521 with
                   | (e,uu____5531) ->
                       let uu____5532 = resugar_term' env e  in
                       (uu____5532, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___73_5557 =
              match uu___73_5557 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5590 = resugar_term' env e  in
                         (uu____5590, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5595 -> aux l tl1)
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
        let uu____5641 = b  in
        match uu____5641 with
        | (x,aq) ->
            let uu____5646 = resugar_arg_qual aq  in
            FStar_Util.map_opt uu____5646
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5660 =
                       let uu____5661 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5661  in
                     FStar_Parser_AST.mk_binder uu____5660 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5662 ->
                     let uu____5663 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5663
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5665 =
                          let uu____5666 =
                            let uu____5671 = bv_as_unique_ident x  in
                            (uu____5671, e)  in
                          FStar_Parser_AST.Annotated uu____5666  in
                        FStar_Parser_AST.mk_binder uu____5665 r
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
              let uu____5691 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5691  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5694 =
                if used
                then
                  let uu____5695 =
                    let uu____5702 = bv_as_unique_ident v1  in
                    (uu____5702, aqual)  in
                  FStar_Parser_AST.PatVar uu____5695
                else FStar_Parser_AST.PatWild  in
              mk1 uu____5694  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5708;
                  FStar_Syntax_Syntax.vars = uu____5709;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5719 = FStar_Options.print_bound_var_types ()  in
                if uu____5719
                then
                  let uu____5720 =
                    let uu____5721 =
                      let uu____5732 =
                        let uu____5739 = resugar_term' env typ  in
                        (uu____5739, FStar_Pervasives_Native.None)  in
                      (pat, uu____5732)  in
                    FStar_Parser_AST.PatAscribed uu____5721  in
                  mk1 uu____5720
                else pat

and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.aqual ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____5757 = resugar_arg_qual qual  in
          FStar_Util.map_opt uu____5757
            (fun aqual  ->
               let uu____5769 =
                 let uu____5774 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                   uu____5774
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5769)

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
          (let uu____5837 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5837) &&
            (let uu____5839 =
               FStar_List.existsML
                 (fun uu____5850  ->
                    match uu____5850 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5866)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5871 -> false
                          | uu____5872 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5839)
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
            let uu____5935 = may_drop_implicits args  in
            if uu____5935 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____5955  ->
                 match uu____5955 with
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
              ((let uu____6001 =
                  let uu____6002 =
                    let uu____6003 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6003  in
                  Prims.op_Negation uu____6002  in
                if uu____6001
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
              let uu____6039 = filter_pattern_imp args  in
              (match uu____6039 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____6079 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____6079 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6095 =
                       let uu____6100 =
                         let uu____6101 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6101
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6100)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6095);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____6144  ->
                        match uu____6144 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____6156 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____6156)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____6160;
                 FStar_Syntax_Syntax.fv_delta = uu____6161;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____6188 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____6188 FStar_List.rev  in
              let args1 =
                let uu____6204 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____6222  ->
                          match uu____6222 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____6204 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6296 = map21 tl1 []  in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6296
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6319 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6319
                 in
              let args2 =
                let uu____6337 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6337 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6379 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6379 with
               | FStar_Pervasives_Native.Some (op,uu____6389) ->
                   let uu____6400 =
                     let uu____6401 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____6401  in
                   mk1 uu____6400
               | FStar_Pervasives_Native.None  ->
                   let uu____6408 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6408 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6413 ->
              mk1 FStar_Parser_AST.PatWild
          | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term)
         in aux p FStar_Pervasives_Native.None

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___74_6428  ->
    match uu___74_6428 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Visible
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
    | FStar_Syntax_Syntax.Logic  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Logic
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____6437 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6438 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6439 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6444 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6453 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6462 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___75_6467  ->
    match uu___75_6467 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts,FStar_Parser_AST.tycon)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun datacon_ses  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid,uvs,bs,t,uu____6503,datacons) ->
            let uu____6513 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6536,uu____6537,uu____6538,inductive_lid,uu____6540,uu____6541)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6546 -> failwith "unexpected"))
               in
            (match uu____6513 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6561 = FStar_Options.print_implicits ()  in
                   if uu____6561 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6575 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___76_6580  ->
                             match uu___76_6580 with
                             | FStar_Syntax_Syntax.RecordType uu____6581 ->
                                 true
                             | uu____6590 -> false))
                      in
                   if uu____6575
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6642,univs1,term,uu____6645,num,uu____6647)
                           ->
                           let uu____6652 =
                             let uu____6653 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6653.FStar_Syntax_Syntax.n  in
                           (match uu____6652 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6667)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6728  ->
                                          match uu____6728 with
                                          | (b,qual) ->
                                              let uu____6743 =
                                                let uu____6744 =
                                                  bv_as_unique_ident b  in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6744
                                                 in
                                              let uu____6745 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6743, uu____6745,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6756 -> failwith "unexpected")
                       | uu____6767 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____6892,num,uu____6894) ->
                            let c =
                              let uu____6912 =
                                let uu____6915 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____6915  in
                              ((l.FStar_Ident.ident), uu____6912,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____6932 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____7006 ->
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
        let uu____7030 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____7030;
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
        let uu____7056 = ts  in
        match uu____7056 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____7068 =
              let uu____7069 =
                let uu____7082 =
                  let uu____7091 =
                    let uu____7098 =
                      let uu____7099 =
                        let uu____7112 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____7112)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____7099  in
                    (uu____7098, FStar_Pervasives_Native.None)  in
                  [uu____7091]  in
                (false, uu____7082)  in
              FStar_Parser_AST.Tycon uu____7069  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____7068
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tsheme" ts 
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
              let uu____7190 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____7190 with
              | (bs,action_defn) ->
                  let uu____7197 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____7197 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____7207 = FStar_Options.print_implicits ()
                            in
                         if uu____7207
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____7214 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____7214 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____7230 =
                             let uu____7241 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____7241,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____7230  in
                         let t =
                           FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un
                            in
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None, t)),
                                   FStar_Pervasives_Native.None)]))
                       else
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None,
                                       action_defn1)),
                                   FStar_Pervasives_Native.None)])))
               in
            let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident
               in
            let uu____7315 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7315 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7325 = FStar_Options.print_implicits ()  in
                  if uu____7325 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7332 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7332 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7400) ->
          let uu____7409 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7431 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7448 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7455 -> false
                    | uu____7470 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7409 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7506 se1 =
                 match uu____7506 with
                 | (datacon_ses1,tycons) ->
                     let uu____7532 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7532 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7547 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7547 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7582 =
                           let uu____7583 =
                             let uu____7584 =
                               let uu____7597 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, uu____7597)  in
                             FStar_Parser_AST.Tycon uu____7584  in
                           decl'_to_decl se uu____7583  in
                         FStar_Pervasives_Native.Some uu____7582
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7628,uu____7629,uu____7630,uu____7631,uu____7632)
                              ->
                              let uu____7637 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7637
                          | uu____7640 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7643 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7649) ->
          let uu____7654 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___77_7660  ->
                    match uu___77_7660 with
                    | FStar_Syntax_Syntax.Projector (uu____7661,uu____7662)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7663 -> true
                    | uu____7664 -> false))
             in
          if uu____7654
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7695) ->
                 let uu____7724 =
                   let uu____7725 =
                     let uu____7726 =
                       let uu____7737 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7737)  in
                     FStar_Parser_AST.TopLevelLet uu____7726  in
                   decl'_to_decl se uu____7725  in
                 FStar_Pervasives_Native.Some uu____7724
             | uu____7774 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7778,fml) ->
          let uu____7780 =
            let uu____7781 =
              let uu____7782 =
                let uu____7787 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7787)  in
              FStar_Parser_AST.Assume uu____7782  in
            decl'_to_decl se uu____7781  in
          FStar_Pervasives_Native.Some uu____7780
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7789 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7789
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7791 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7791
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7800,t) ->
                let uu____7810 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7810
            | uu____7811 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7819,t) ->
                let uu____7829 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7829
            | uu____7830 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7854 -> failwith "Should not happen hopefully"  in
          let uu____7863 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____7863
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____7873 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7873 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____7885 = FStar_Options.print_implicits ()  in
                 if uu____7885 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____7898 =
                 let uu____7899 =
                   let uu____7900 =
                     let uu____7913 =
                       let uu____7922 =
                         let uu____7929 =
                           let uu____7930 =
                             let uu____7943 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____7943)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____7930  in
                         (uu____7929, FStar_Pervasives_Native.None)  in
                       [uu____7922]  in
                     (false, uu____7913)  in
                   FStar_Parser_AST.Tycon uu____7900  in
                 decl'_to_decl se uu____7899  in
               FStar_Pervasives_Native.Some uu____7898)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____7971 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____7971
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____7975 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___78_7981  ->
                    match uu___78_7981 with
                    | FStar_Syntax_Syntax.Projector (uu____7982,uu____7983)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7984 -> true
                    | uu____7985 -> false))
             in
          if uu____7975
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____7990 =
                 (let uu____7993 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____7993) || (FStar_List.isEmpty uvs)
                  in
               if uu____7990
               then resugar_term' env t
               else
                 (let uu____7995 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____7995 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____8003 = resugar_term' env t1  in
                      label universes uu____8003)
                in
             let uu____8004 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____8004)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____8011 =
            let uu____8012 =
              let uu____8013 =
                let uu____8020 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____8025 = resugar_term' env t  in
                (uu____8020, uu____8025)  in
              FStar_Parser_AST.Splice uu____8013  in
            decl'_to_decl se uu____8012  in
          FStar_Pervasives_Native.Some uu____8011
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8028 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____8045 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____8060 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) = FStar_Syntax_DsEnv.empty_env () 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____8081 = noenv resugar_term'  in uu____8081 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____8098 = noenv resugar_sigelt'  in uu____8098 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____8115 = noenv resugar_comp'  in uu____8115 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____8137 = noenv resugar_pat'  in uu____8137 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____8170 = noenv resugar_binder'  in uu____8170 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____8194 = noenv resugar_tscheme'  in uu____8194 ts 
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
          let uu____8226 = noenv resugar_eff_decl'  in
          uu____8226 for_free r q ed
  