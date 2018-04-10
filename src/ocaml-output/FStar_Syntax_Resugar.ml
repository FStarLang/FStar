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
    Prims.unit ->
      ('Auu____26 -> 'Auu____27 FStar_Pervasives_Native.option) ->
        'Auu____26 Prims.list -> 'Auu____27 Prims.list
  =
  fun a246  ->
    fun a247  ->
      fun a248  ->
        (Obj.magic (fun uu____43  -> FStar_List.filter_map)) a246 a247 a248
  
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
      | FStar_Syntax_Syntax.U_succ uu____309 ->
          let uu____310 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____310 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____317 =
                      let uu____318 =
                        let uu____319 =
                          let uu____330 = FStar_Util.string_of_int n1  in
                          (uu____330, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____319  in
                      FStar_Parser_AST.Const uu____318  in
                    mk1 uu____317 r
                | uu____341 ->
                    let e1 =
                      let uu____343 =
                        let uu____344 =
                          let uu____345 =
                            let uu____356 = FStar_Util.string_of_int n1  in
                            (uu____356, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____345  in
                        FStar_Parser_AST.Const uu____344  in
                      mk1 uu____343 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____368 =
                      let uu____369 =
                        let uu____376 = FStar_Ident.id_of_text "+"  in
                        (uu____376, [e1; e2])  in
                      FStar_Parser_AST.Op uu____369  in
                    mk1 uu____368 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____382 ->
               let t =
                 let uu____386 =
                   let uu____387 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____387  in
                 mk1 uu____386 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____393 =
                        let uu____394 =
                          let uu____401 = resugar_universe x r  in
                          (acc, uu____401, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____394  in
                      mk1 uu____393 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____403 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____414 =
              let uu____419 =
                let uu____420 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____420  in
              (uu____419, r)  in
            FStar_Ident.mk_ident uu____414  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string,Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___68_446 =
      match uu___68_446 with
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
      | uu____623 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____670 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____682 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____682 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____692 ->
               let op =
                 let uu____696 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____738) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____696
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
      let uu____945 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____945 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____999 ->
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
                (let uu____1070 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1070
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1094 =
      let uu____1095 = FStar_Syntax_Subst.compress t  in
      uu____1095.FStar_Syntax_Syntax.n  in
    match uu____1094 with
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
        let uu____1118 = string_to_op s  in
        (match uu____1118 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1152 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1167 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1177 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1183 -> true
    | uu____1184 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1195 ->
        let uu____1196 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1196
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1208 = may_shorten lid  in
      if uu____1208 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1318 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1318  in
      let uu____1319 =
        let uu____1320 = FStar_Syntax_Subst.compress t  in
        uu____1320.FStar_Syntax_Syntax.n  in
      match uu____1319 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1323 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1349 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1349
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1352 =
              let uu____1355 = bv_as_unique_ident x  in [uu____1355]  in
            FStar_Ident.lid_of_ids uu____1352  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1358 =
              let uu____1361 = bv_as_unique_ident x  in [uu____1361]  in
            FStar_Ident.lid_of_ids uu____1358  in
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
            let uu____1379 =
              let uu____1380 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1380  in
            mk1 uu____1379
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
               | uu____1390 -> failwith "wrong projector format")
            else
              (let uu____1394 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1397 =
                      let uu____1399 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1399  in
                    let uu____1401 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1397 <> uu____1401)
                  in
               if uu____1394
               then
                 let uu____1404 =
                   let uu____1405 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1405  in
                 mk1 uu____1404
               else
                 (let uu____1407 =
                    let uu____1408 =
                      let uu____1419 = maybe_shorten_fv env fv  in
                      (uu____1419, [])  in
                    FStar_Parser_AST.Construct uu____1408  in
                  mk1 uu____1407))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1437 = FStar_Options.print_universes ()  in
          if uu____1437
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
                   let uu____1466 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1466  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1489 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1496 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1496
          then
            let uu____1497 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1497
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1500 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1509 -> ("Type", true)  in
          (match uu____1500 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1513 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1513  in
               let uu____1514 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1514
               then
                 let uu____1515 =
                   let uu____1516 =
                     let uu____1523 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1523, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1516  in
                 mk1 uu____1515
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1527) ->
          let uu____1548 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1548 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1556 = FStar_Options.print_implicits ()  in
                 if uu____1556 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1573  ->
                         match uu____1573 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____1603 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1603 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1611 = FStar_Options.print_implicits ()  in
                 if uu____1611 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1617 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1617 FStar_List.rev  in
               let rec aux body3 uu___69_1638 =
                 match uu___69_1638 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1654 =
            let uu____1659 =
              let uu____1660 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1660]  in
            FStar_Syntax_Subst.open_term uu____1659 phi  in
          (match uu____1654 with
           | (x1,phi1) ->
               let b =
                 let uu____1664 =
                   let uu____1667 = FStar_List.hd x1  in
                   resugar_binder' env uu____1667 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1664  in
               let uu____1672 =
                 let uu____1673 =
                   let uu____1678 = resugar_term' env phi1  in
                   (b, uu____1678)  in
                 FStar_Parser_AST.Refine uu____1673  in
               mk1 uu____1672)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1680;
             FStar_Syntax_Syntax.vars = uu____1681;_},(e,uu____1683)::[])
          when
          (let uu____1714 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1714) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___70_1757 =
            match uu___70_1757 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1827 -> failwith "last of an empty list"  in
          let rec last_two uu___71_1864 =
            match uu___71_1864 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1895::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____1972::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2041  ->
                   match uu____2041 with
                   | (e2,qual) ->
                       let uu____2058 = resugar_term' env e2  in
                       let uu____2059 = resugar_imp qual  in
                       (uu____2058, uu____2059)) args1
               in
            let uu____2060 = resugar_term' env e1  in
            match uu____2060 with
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
                     fun uu____2097  ->
                       match uu____2097 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2113 = FStar_Options.print_implicits ()  in
            if uu____2113 then args else filter_imp args  in
          let uu____2125 = resugar_term_as_op e  in
          (match uu____2125 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2136) ->
               (match args1 with
                | (fst1,uu____2142)::(snd1,uu____2144)::rest ->
                    let e1 =
                      let uu____2175 =
                        let uu____2176 =
                          let uu____2183 = FStar_Ident.id_of_text "*"  in
                          let uu____2184 =
                            let uu____2187 = resugar_term' env fst1  in
                            let uu____2188 =
                              let uu____2191 = resugar_term' env snd1  in
                              [uu____2191]  in
                            uu____2187 :: uu____2188  in
                          (uu____2183, uu____2184)  in
                        FStar_Parser_AST.Op uu____2176  in
                      mk1 uu____2175  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2204  ->
                           match uu____2204 with
                           | (x,uu____2210) ->
                               let uu____2211 =
                                 let uu____2212 =
                                   let uu____2219 =
                                     FStar_Ident.id_of_text "*"  in
                                   let uu____2220 =
                                     let uu____2223 =
                                       let uu____2226 = resugar_term' env x
                                          in
                                       [uu____2226]  in
                                     e1 :: uu____2223  in
                                   (uu____2219, uu____2220)  in
                                 FStar_Parser_AST.Op uu____2212  in
                               mk1 uu____2211) e1 rest
                | uu____2229 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2238) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2264)::[] -> b
                 | uu____2281 -> failwith "wrong arguments to dtuple"  in
               let uu____2292 =
                 let uu____2293 = FStar_Syntax_Subst.compress body  in
                 uu____2293.FStar_Syntax_Syntax.n  in
               (match uu____2292 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2298) ->
                    let uu____2319 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2319 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2327 = FStar_Options.print_implicits ()
                              in
                           if uu____2327 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2339 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2360  ->
                              match uu____2360 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2372) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2378) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2383 = FStar_List.hd args1  in
               (match uu____2383 with
                | (t1,uu____2397) ->
                    let uu____2402 =
                      let uu____2403 = FStar_Syntax_Subst.compress t1  in
                      uu____2403.FStar_Syntax_Syntax.n  in
                    (match uu____2402 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2408 =
                           let uu____2409 =
                             let uu____2414 = resugar_term' env t1  in
                             (uu____2414, f)  in
                           FStar_Parser_AST.Project uu____2409  in
                         mk1 uu____2408
                     | uu____2415 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2416) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2436 =
                 match new_args with
                 | (a1,uu____2454)::(a2,uu____2456)::[] -> (a1, a2)
                 | uu____2487 -> failwith "wrong arguments to try_with"  in
               (match uu____2436 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2519 =
                        let uu____2520 = FStar_Syntax_Subst.compress term  in
                        uu____2520.FStar_Syntax_Syntax.n  in
                      match uu____2519 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2525) ->
                          let uu____2546 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2546 with | (x1,e2) -> e2)
                      | uu____2553 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2555 = decomp body  in
                      resugar_term' env uu____2555  in
                    let handler1 =
                      let uu____2557 = decomp handler  in
                      resugar_term' env uu____2557  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2564,uu____2565,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2597,uu____2598,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2635 =
                            let uu____2636 =
                              let uu____2645 = resugar_body t11  in
                              (uu____2645, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2636  in
                          mk1 uu____2635
                      | uu____2648 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2704 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2734) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2740) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2828 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2840 =
                   let uu____2841 = FStar_Syntax_Subst.compress body  in
                   uu____2841.FStar_Syntax_Syntax.n  in
                 match uu____2840 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2846) ->
                     let uu____2867 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2867 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2875 = FStar_Options.print_implicits ()
                               in
                            if uu____2875 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2884 =
                            let uu____2893 =
                              let uu____2894 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2894.FStar_Syntax_Syntax.n  in
                            match uu____2893 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____2912 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____2940 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____2976  ->
                                                     match uu____2976 with
                                                     | (e2,uu____2982) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____2940, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____2990 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____2990)
                                  | uu____2997 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____2912 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3028 ->
                                let uu____3029 = resugar_term' env body2  in
                                ([], uu____3029)
                             in
                          (match uu____2884 with
                           | (pats,body3) ->
                               let uu____3046 = uncurry xs3 pats body3  in
                               (match uu____3046 with
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
                 | uu____3094 ->
                     if op = "forall"
                     then
                       let uu____3095 =
                         let uu____3096 =
                           let uu____3109 = resugar_term' env body  in
                           ([], [[]], uu____3109)  in
                         FStar_Parser_AST.QForall uu____3096  in
                       mk1 uu____3095
                     else
                       (let uu____3121 =
                          let uu____3122 =
                            let uu____3135 = resugar_term' env body  in
                            ([], [[]], uu____3135)  in
                          FStar_Parser_AST.QExists uu____3122  in
                        mk1 uu____3121)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3162)::[] -> resugar b
                  | uu____3179 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3189) ->
               let uu____3194 = FStar_List.hd args1  in
               (match uu____3194 with
                | (e1,uu____3208) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3276  ->
                         match uu____3276 with
                         | (e1,qual) ->
                             let uu____3293 = resugar_term' env e1  in
                             let uu____3294 = resugar_imp qual  in
                             (uu____3293, uu____3294)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3307 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3307 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3355 =
                               let uu____3356 =
                                 let uu____3363 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3363)  in
                               FStar_Parser_AST.Op uu____3356  in
                             mk1 uu____3355  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3381  ->
                                  match uu____3381 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3396 =
                      let uu____3397 =
                        let uu____3404 =
                          let uu____3407 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3407
                           in
                        (op1, uu____3404)  in
                      FStar_Parser_AST.Op uu____3397  in
                    mk1 uu____3396
                | uu____3420 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3489 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3489 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3535 =
                   let uu____3548 =
                     let uu____3553 = resugar_pat' env pat1 branch_bv  in
                     let uu____3554 = resugar_term' env e  in
                     (uu____3553, uu____3554)  in
                   (FStar_Pervasives_Native.None, uu____3548)  in
                 [uu____3535]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3606,t1)::(pat2,uu____3609,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3705 =
            let uu____3706 =
              let uu____3713 = resugar_term' env e  in
              let uu____3714 = resugar_term' env t1  in
              let uu____3715 = resugar_term' env t2  in
              (uu____3713, uu____3714, uu____3715)  in
            FStar_Parser_AST.If uu____3706  in
          mk1 uu____3705
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3780 =
            match uu____3780 with
            | (pat,wopt,b) ->
                let uu____3822 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3822 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3874 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3874
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3878 =
            let uu____3879 =
              let uu____3894 = resugar_term' env e  in
              let uu____3895 = FStar_List.map resugar_branch branches  in
              (uu____3894, uu____3895)  in
            FStar_Parser_AST.Match uu____3879  in
          mk1 uu____3878
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3941) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4008 =
            let uu____4009 =
              let uu____4018 = resugar_term' env e  in
              (uu____4018, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4009  in
          mk1 uu____4008
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4043 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4043 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4095 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4095
                    in
                 let uu____4100 =
                   let uu____4105 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4105
                    in
                 match uu____4100 with
                 | (univs1,td) ->
                     let uu____4124 =
                       let uu____4133 =
                         let uu____4134 = FStar_Syntax_Subst.compress td  in
                         uu____4134.FStar_Syntax_Syntax.n  in
                       match uu____4133 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4145,(t1,uu____4147)::(d,uu____4149)::[])
                           -> (t1, d)
                       | uu____4192 -> failwith "wrong let binding format"
                        in
                     (match uu____4124 with
                      | (typ,def) ->
                          let uu____4227 =
                            let uu____4234 =
                              let uu____4235 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4235.FStar_Syntax_Syntax.n  in
                            match uu____4234 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4246) ->
                                let uu____4267 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4267 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4281 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4281
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4283 -> ([], def, false)  in
                          (match uu____4227 with
                           | (binders,term,is_pat_app) ->
                               let uu____4315 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4326 =
                                       let uu____4327 =
                                         let uu____4328 =
                                           let uu____4335 =
                                             bv_as_unique_ident bv  in
                                           (uu____4335,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4328
                                          in
                                       mk_pat uu____4327  in
                                     (uu____4326, term)
                                  in
                               (match uu____4315 with
                                | (pat,term1) ->
                                    let uu____4356 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4388  ->
                                                  match uu____4388 with
                                                  | (bv,q) ->
                                                      let uu____4403 =
                                                        resugar_arg_qual q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4403
                                                        (fun q1  ->
                                                           let uu____4415 =
                                                             let uu____4416 =
                                                               let uu____4423
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4423,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4416
                                                              in
                                                           mk_pat uu____4415)))
                                           in
                                        let uu____4426 =
                                          let uu____4431 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4431)
                                           in
                                        let uu____4434 =
                                          universe_to_string univs1  in
                                        (uu____4426, uu____4434)
                                      else
                                        (let uu____4440 =
                                           let uu____4445 =
                                             resugar_term' env term1  in
                                           (pat, uu____4445)  in
                                         let uu____4446 =
                                           universe_to_string univs1  in
                                         (uu____4440, uu____4446))
                                       in
                                    (attrs_opt, uu____4356))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4545 =
                   match uu____4545 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4601 =
                         let uu____4602 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4602  in
                       if uu____4601
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4677) ->
          let s =
            let uu____4703 =
              let uu____4704 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_All.pipe_right uu____4704 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4703  in
          let uu____4705 = mk1 FStar_Parser_AST.Wild  in label s uu____4705
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____4713 =
            let uu____4714 =
              let uu____4719 = resugar_term' env tm  in (uu____4719, qi1)  in
            FStar_Parser_AST.Quote uu____4714  in
          mk1 uu____4713
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___72_4730 =
            match uu___72_4730 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4737,(uu____4738,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____4799 =
                        let uu____4800 =
                          let uu____4809 = resugar_seq t11  in
                          (uu____4809, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____4800  in
                      mk1 uu____4799
                  | uu____4812 -> t1  in
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
                 | uu____4858 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval  ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                let uu____4860 =
                  let uu____4861 = FStar_Syntax_Subst.compress e  in
                  uu____4861.FStar_Syntax_Syntax.n  in
                (match uu____4860 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____4865;
                        FStar_Syntax_Syntax.vars = uu____4866;_},(term,uu____4868)::[])
                     -> resugar_term' env term
                 | uu____4897 -> failwith "mutable_rval should have app term")
             in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____4935  ->
                         match uu____4935 with
                         | (x,uu____4941) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l,uu____4943,p) ->
               let uu____4945 =
                 let uu____4946 =
                   let uu____4953 = resugar_term' env e  in
                   (uu____4953, l, p)  in
                 FStar_Parser_AST.Labeled uu____4946  in
               mk1 uu____4945
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____4962 =
                 let uu____4963 =
                   let uu____4972 = resugar_term' env e  in
                   let uu____4973 =
                     let uu____4974 =
                       let uu____4975 =
                         let uu____4986 =
                           let uu____4993 =
                             let uu____4998 = resugar_term' env t1  in
                             (uu____4998, FStar_Parser_AST.Nothing)  in
                           [uu____4993]  in
                         (name1, uu____4986)  in
                       FStar_Parser_AST.Construct uu____4975  in
                     mk1 uu____4974  in
                   (uu____4972, uu____4973, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____4963  in
               mk1 uu____4962
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5016,t1) ->
               let uu____5022 =
                 let uu____5023 =
                   let uu____5032 = resugar_term' env e  in
                   let uu____5033 =
                     let uu____5034 =
                       let uu____5035 =
                         let uu____5046 =
                           let uu____5053 =
                             let uu____5058 = resugar_term' env t1  in
                             (uu____5058, FStar_Parser_AST.Nothing)  in
                           [uu____5053]  in
                         (name1, uu____5046)  in
                       FStar_Parser_AST.Construct uu____5035  in
                     mk1 uu____5034  in
                   (uu____5032, uu____5033, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5023  in
               mk1 uu____5022)
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
               let uu____5108 = FStar_Options.print_universes ()  in
               if uu____5108
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
               let uu____5169 = FStar_Options.print_universes ()  in
               if uu____5169
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
            let uu____5210 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5210, FStar_Parser_AST.Nothing)  in
          let uu____5211 = FStar_Options.print_effect_args ()  in
          if uu____5211
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____5232 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____5232
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5301 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5301, (FStar_Pervasives_Native.snd post))  in
                    let uu____5310 =
                      let uu____5319 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5319 then [] else [pre]  in
                    let uu____5349 =
                      let uu____5358 =
                        let uu____5367 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5367 then [] else [pats]  in
                      FStar_List.append [post1] uu____5358  in
                    FStar_List.append uu____5310 uu____5349
                | uu____5421 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5450  ->
                   match uu____5450 with
                   | (e,uu____5460) ->
                       let uu____5461 = resugar_term' env e  in
                       (uu____5461, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___73_5484 =
              match uu___73_5484 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5517 = resugar_term' env e  in
                         (uu____5517, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5522 -> aux l tl1)
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
        let uu____5568 = b  in
        match uu____5568 with
        | (x,aq) ->
            let uu____5573 = resugar_arg_qual aq  in
            FStar_Util.map_opt uu____5573
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5587 =
                       let uu____5588 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5588  in
                     FStar_Parser_AST.mk_binder uu____5587 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5589 ->
                     let uu____5590 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5590
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5592 =
                          let uu____5593 =
                            let uu____5598 = bv_as_unique_ident x  in
                            (uu____5598, e)  in
                          FStar_Parser_AST.Annotated uu____5593  in
                        FStar_Parser_AST.mk_binder uu____5592 r
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
              let uu____5617 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5617  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5620 =
                if used
                then
                  let uu____5621 =
                    let uu____5628 = bv_as_unique_ident v1  in
                    (uu____5628, aqual)  in
                  FStar_Parser_AST.PatVar uu____5621
                else FStar_Parser_AST.PatWild  in
              mk1 uu____5620  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5634;
                  FStar_Syntax_Syntax.vars = uu____5635;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5645 = FStar_Options.print_bound_var_types ()  in
                if uu____5645
                then
                  let uu____5646 =
                    let uu____5647 =
                      let uu____5658 =
                        let uu____5665 = resugar_term' env typ  in
                        (uu____5665, FStar_Pervasives_Native.None)  in
                      (pat, uu____5658)  in
                    FStar_Parser_AST.PatAscribed uu____5647  in
                  mk1 uu____5646
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
          let uu____5683 = resugar_arg_qual qual  in
          FStar_Util.map_opt uu____5683
            (fun aqual  ->
               let uu____5695 =
                 let uu____5700 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                   uu____5700
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5695)

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
          (let uu____5752 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5752) &&
            (let uu____5754 =
               FStar_List.existsML
                 (fun uu____5765  ->
                    match uu____5765 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5781)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5786 -> false
                          | uu____5787 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5754)
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
            let uu____5846 = may_drop_implicits args  in
            if uu____5846 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____5868  ->
                 match uu____5868 with
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
              let uu____5913 =
                let uu____5914 =
                  let uu____5915 =
                    let uu____5916 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____5916  in
                  Prims.op_Negation uu____5915  in
                if uu____5914
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ()  in
              mk1 (FStar_Parser_AST.PatList [])
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____5952 = filter_pattern_imp args  in
              (match uu____5952 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____5992 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____5992 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   let uu____6007 =
                     let uu____6008 =
                       let uu____6013 =
                         let uu____6014 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6014
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6013)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6008
                      in
                   resugar_plain_pat_cons fv args)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____6059  ->
                        match uu____6059 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____6071 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____6071)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____6075;
                 FStar_Syntax_Syntax.fv_delta = uu____6076;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____6103 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____6103 FStar_List.rev  in
              let args1 =
                let uu____6119 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____6139  ->
                          match uu____6139 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____6119 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6211 = map21 tl1 []  in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6211
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6234 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6234
                 in
              let args2 =
                let uu____6252 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6252 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6294 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6294 with
               | FStar_Pervasives_Native.Some (op,uu____6304) ->
                   let uu____6315 =
                     let uu____6316 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____6316  in
                   mk1 uu____6315
               | FStar_Pervasives_Native.None  ->
                   let uu____6323 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6323 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6328 ->
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
  fun uu___74_6343  ->
    match uu___74_6343 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6352 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6353 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6354 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6359 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6368 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6377 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___75_6382  ->
    match uu___75_6382 with
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
            (tylid,uvs,bs,t,uu____6418,datacons) ->
            let uu____6428 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6455,uu____6456,uu____6457,inductive_lid,uu____6459,uu____6460)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6465 -> failwith "unexpected"))
               in
            (match uu____6428 with
             | (current_datacons,other_datacons) ->
                 let uu____6480 = ()  in
                 let bs1 =
                   let uu____6482 = FStar_Options.print_implicits ()  in
                   if uu____6482 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6492 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___76_6497  ->
                             match uu___76_6497 with
                             | FStar_Syntax_Syntax.RecordType uu____6498 ->
                                 true
                             | uu____6507 -> false))
                      in
                   if uu____6492
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6557,univs1,term,uu____6560,num,uu____6562)
                           ->
                           let uu____6567 =
                             let uu____6568 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6568.FStar_Syntax_Syntax.n  in
                           (match uu____6567 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6582)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6643  ->
                                          match uu____6643 with
                                          | (b,qual) ->
                                              let uu____6658 =
                                                let uu____6659 =
                                                  bv_as_unique_ident b  in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6659
                                                 in
                                              let uu____6660 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6658, uu____6660,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6671 -> failwith "unexpected")
                       | uu____6682 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____6805,num,uu____6807) ->
                            let c =
                              let uu____6825 =
                                let uu____6828 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____6828  in
                              ((l.FStar_Ident.ident), uu____6825,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____6845 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____6921 ->
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
        let uu____6945 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6945;
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
        let uu____6971 = ts  in
        match uu____6971 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____6979 =
              let uu____6980 =
                let uu____6993 =
                  let uu____7002 =
                    let uu____7009 =
                      let uu____7010 =
                        let uu____7023 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____7023)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____7010  in
                    (uu____7009, FStar_Pervasives_Native.None)  in
                  [uu____7002]  in
                (false, uu____6993)  in
              FStar_Parser_AST.Tycon uu____6980  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6979
  
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
              let uu____7099 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____7099 with
              | (bs,action_defn) ->
                  let uu____7106 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____7106 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____7114 = FStar_Options.print_implicits ()
                            in
                         if uu____7114
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____7119 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____7119 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____7133 =
                             let uu____7144 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____7144,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____7133  in
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
            let uu____7218 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7218 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7226 = FStar_Options.print_implicits ()  in
                  if uu____7226 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7231 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7231 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7295) ->
          let uu____7304 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7326 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7343 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7350 -> false
                    | uu____7365 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7304 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7399 se1 =
                 match uu____7399 with
                 | (datacon_ses1,tycons) ->
                     let uu____7425 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7425 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7440 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7440 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7475 =
                           let uu____7476 =
                             let uu____7477 =
                               let uu____7490 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, uu____7490)  in
                             FStar_Parser_AST.Tycon uu____7477  in
                           decl'_to_decl se uu____7476  in
                         FStar_Pervasives_Native.Some uu____7475
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7521,uu____7522,uu____7523,uu____7524,uu____7525)
                              ->
                              let uu____7530 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7530
                          | uu____7533 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7536 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7542) ->
          let uu____7547 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___77_7553  ->
                    match uu___77_7553 with
                    | FStar_Syntax_Syntax.Projector (uu____7554,uu____7555)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7556 -> true
                    | uu____7557 -> false))
             in
          if uu____7547
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7581) ->
                 let uu____7610 =
                   let uu____7611 =
                     let uu____7612 =
                       let uu____7623 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7623)  in
                     FStar_Parser_AST.TopLevelLet uu____7612  in
                   decl'_to_decl se uu____7611  in
                 FStar_Pervasives_Native.Some uu____7610
             | uu____7660 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7664,fml) ->
          let uu____7666 =
            let uu____7667 =
              let uu____7668 =
                let uu____7673 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7673)  in
              FStar_Parser_AST.Assume uu____7668  in
            decl'_to_decl se uu____7667  in
          FStar_Pervasives_Native.Some uu____7666
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7675 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7675
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7677 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7677
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7686,t) ->
                let uu____7698 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7698
            | uu____7699 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7707,t) ->
                let uu____7719 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7719
            | uu____7720 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7744 -> failwith "Should not happen hopefully"  in
          let uu____7753 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____7753
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____7763 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7763 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____7773 = FStar_Options.print_implicits ()  in
                 if uu____7773 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____7782 =
                 let uu____7783 =
                   let uu____7784 =
                     let uu____7797 =
                       let uu____7806 =
                         let uu____7813 =
                           let uu____7814 =
                             let uu____7827 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____7827)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____7814  in
                         (uu____7813, FStar_Pervasives_Native.None)  in
                       [uu____7806]  in
                     (false, uu____7797)  in
                   FStar_Parser_AST.Tycon uu____7784  in
                 decl'_to_decl se uu____7783  in
               FStar_Pervasives_Native.Some uu____7782)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____7855 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____7855
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____7859 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___78_7865  ->
                    match uu___78_7865 with
                    | FStar_Syntax_Syntax.Projector (uu____7866,uu____7867)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7868 -> true
                    | uu____7869 -> false))
             in
          if uu____7859
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____7874 =
                 (let uu____7877 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____7877) || (FStar_List.isEmpty uvs)
                  in
               if uu____7874
               then resugar_term' env t
               else
                 (let uu____7879 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____7879 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____7887 = resugar_term' env t1  in
                      label universes uu____7887)
                in
             let uu____7888 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____7888)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____7895 =
            let uu____7896 =
              let uu____7897 =
                let uu____7904 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____7909 = resugar_term' env t  in
                (uu____7904, uu____7909)  in
              FStar_Parser_AST.Splice uu____7897  in
            decl'_to_decl se uu____7896  in
          FStar_Pervasives_Native.Some uu____7895
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7912 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____7929 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____7944 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) = FStar_Syntax_DsEnv.empty_env () 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____7965 = noenv resugar_term'  in uu____7965 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____7981 = noenv resugar_sigelt'  in uu____7981 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____7997 = noenv resugar_comp'  in uu____7997 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____8018 = noenv resugar_pat'  in uu____8018 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____8049 = noenv resugar_binder'  in uu____8049 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____8071 = noenv resugar_tscheme'  in uu____8071 ts 
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
          let uu____8102 = noenv resugar_eff_decl'  in
          uu____8102 for_free r q ed
  