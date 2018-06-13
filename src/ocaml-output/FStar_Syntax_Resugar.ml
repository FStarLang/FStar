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
         (fun uu___187_112  ->
            match uu___187_112 with
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
    let name_of_op uu___188_449 =
      match uu___188_449 with
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
  
type expected_arity = Prims.int FStar_Pervasives_Native.option
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
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
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
          let uu____1352 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1352
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1355 =
              let uu____1358 = bv_as_unique_ident x  in [uu____1358]  in
            FStar_Ident.lid_of_ids uu____1355  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1361 =
              let uu____1364 = bv_as_unique_ident x  in [uu____1364]  in
            FStar_Ident.lid_of_ids uu____1361  in
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
            let uu____1382 =
              let uu____1383 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1383  in
            mk1 uu____1382
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
               | uu____1393 -> failwith "wrong projector format")
            else
              (let uu____1397 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1400 =
                      let uu____1402 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1402  in
                    let uu____1404 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1400 <> uu____1404)
                  in
               if uu____1397
               then
                 let uu____1407 =
                   let uu____1408 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1408  in
                 mk1 uu____1407
               else
                 (let uu____1410 =
                    let uu____1411 =
                      let uu____1422 = maybe_shorten_fv env fv  in
                      (uu____1422, [])  in
                    FStar_Parser_AST.Construct uu____1411  in
                  mk1 uu____1410))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1440 = FStar_Options.print_universes ()  in
          if uu____1440
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
                   let uu____1469 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1469  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1492 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1499 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1499
          then
            let uu____1500 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1500
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1503 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1512 -> ("Type", true)  in
          (match uu____1503 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1516 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1516  in
               let uu____1517 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1517
               then
                 let uu____1518 =
                   let uu____1519 =
                     let uu____1526 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1526, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1519  in
                 mk1 uu____1518
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1530) ->
          let uu____1551 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1551 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1565 = FStar_Options.print_implicits ()  in
                 if uu____1565 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1594  ->
                         match uu____1594 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____1624 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1624 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1634 = FStar_Options.print_implicits ()  in
                 if uu____1634 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1642 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1642 FStar_List.rev  in
               let rec aux body3 uu___189_1667 =
                 match uu___189_1667 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1683 =
            let uu____1688 =
              let uu____1689 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1689]  in
            FStar_Syntax_Subst.open_term uu____1688 phi  in
          (match uu____1683 with
           | (x1,phi1) ->
               let b =
                 let uu____1705 =
                   let uu____1708 = FStar_List.hd x1  in
                   resugar_binder' env uu____1708 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1705  in
               let uu____1713 =
                 let uu____1714 =
                   let uu____1719 = resugar_term' env phi1  in
                   (b, uu____1719)  in
                 FStar_Parser_AST.Refine uu____1714  in
               mk1 uu____1713)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1721;
             FStar_Syntax_Syntax.vars = uu____1722;_},(e,uu____1724)::[])
          when
          (let uu____1755 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1755) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___190_1799 =
            match uu___190_1799 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1869 -> failwith "last of an empty list"  in
          let rec last_two uu___191_1907 =
            match uu___191_1907 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1938::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2015::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2086  ->
                   match uu____2086 with
                   | (e2,qual) ->
                       let uu____2103 = resugar_term' env e2  in
                       let uu____2104 = resugar_imp qual  in
                       (uu____2103, uu____2104)) args1
               in
            let uu____2105 = resugar_term' env e1  in
            match uu____2105 with
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
                     fun uu____2142  ->
                       match uu____2142 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2158 = FStar_Options.print_implicits ()  in
            if uu____2158 then args else filter_imp args  in
          let uu____2170 = resugar_term_as_op e  in
          (match uu____2170 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2181) ->
               (match args1 with
                | (fst1,uu____2187)::(snd1,uu____2189)::rest ->
                    let e1 =
                      let uu____2220 =
                        let uu____2221 =
                          let uu____2228 = FStar_Ident.id_of_text "*"  in
                          let uu____2229 =
                            let uu____2232 = resugar_term' env fst1  in
                            let uu____2233 =
                              let uu____2236 = resugar_term' env snd1  in
                              [uu____2236]  in
                            uu____2232 :: uu____2233  in
                          (uu____2228, uu____2229)  in
                        FStar_Parser_AST.Op uu____2221  in
                      mk1 uu____2220  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2251  ->
                           match uu____2251 with
                           | (x,uu____2259) ->
                               let uu____2264 =
                                 let uu____2265 =
                                   let uu____2272 =
                                     FStar_Ident.id_of_text "*"  in
                                   let uu____2273 =
                                     let uu____2276 =
                                       let uu____2279 = resugar_term' env x
                                          in
                                       [uu____2279]  in
                                     e1 :: uu____2276  in
                                   (uu____2272, uu____2273)  in
                                 FStar_Parser_AST.Op uu____2265  in
                               mk1 uu____2264) e1 rest
                | uu____2282 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2291) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2313)::[] -> b
                 | uu____2330 -> failwith "wrong arguments to dtuple"  in
               let uu____2339 =
                 let uu____2340 = FStar_Syntax_Subst.compress body  in
                 uu____2340.FStar_Syntax_Syntax.n  in
               (match uu____2339 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2345) ->
                    let uu____2366 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2366 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2376 = FStar_Options.print_implicits ()
                              in
                           if uu____2376 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2392 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2415  ->
                              match uu____2415 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2433) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2439) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2444 = FStar_List.hd args1  in
               (match uu____2444 with
                | (t1,uu____2458) ->
                    let uu____2463 =
                      let uu____2464 = FStar_Syntax_Subst.compress t1  in
                      uu____2464.FStar_Syntax_Syntax.n  in
                    (match uu____2463 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2469 =
                           let uu____2470 =
                             let uu____2475 = resugar_term' env t1  in
                             (uu____2475, f)  in
                           FStar_Parser_AST.Project uu____2470  in
                         mk1 uu____2469
                     | uu____2476 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2477) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2497 =
                 match new_args with
                 | (a1,uu____2507)::(a2,uu____2509)::[] -> (a1, a2)
                 | uu____2536 -> failwith "wrong arguments to try_with"  in
               (match uu____2497 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2557 =
                        let uu____2558 = FStar_Syntax_Subst.compress term  in
                        uu____2558.FStar_Syntax_Syntax.n  in
                      match uu____2557 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2563) ->
                          let uu____2584 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2584 with | (x1,e2) -> e2)
                      | uu____2591 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2593 = decomp body  in
                      resugar_term' env uu____2593  in
                    let handler1 =
                      let uu____2595 = decomp handler  in
                      resugar_term' env uu____2595  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2603,uu____2604,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2636,uu____2637,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2674 =
                            let uu____2675 =
                              let uu____2684 = resugar_body t11  in
                              (uu____2684, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2675  in
                          mk1 uu____2674
                      | uu____2687 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2744 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2774) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2780) when
               (((op = "=") || (op = "==")) || (op = "===")) &&
                 (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2786) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2877 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2890 =
                   let uu____2891 = FStar_Syntax_Subst.compress body  in
                   uu____2891.FStar_Syntax_Syntax.n  in
                 match uu____2890 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2896) ->
                     let uu____2917 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2917 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2927 = FStar_Options.print_implicits ()
                               in
                            if uu____2927 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2940 =
                            let uu____2949 =
                              let uu____2950 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2950.FStar_Syntax_Syntax.n  in
                            match uu____2949 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____2968 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____2996 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3032  ->
                                                     match uu____3032 with
                                                     | (e2,uu____3038) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____2996, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3046 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3046)
                                  | uu____3053 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____2968 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3084 ->
                                let uu____3085 = resugar_term' env body2  in
                                ([], uu____3085)
                             in
                          (match uu____2940 with
                           | (pats,body3) ->
                               let uu____3102 = uncurry xs3 pats body3  in
                               (match uu____3102 with
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
                 | uu____3150 ->
                     if op = "forall"
                     then
                       let uu____3151 =
                         let uu____3152 =
                           let uu____3165 = resugar_term' env body  in
                           ([], [[]], uu____3165)  in
                         FStar_Parser_AST.QForall uu____3152  in
                       mk1 uu____3151
                     else
                       (let uu____3177 =
                          let uu____3178 =
                            let uu____3191 = resugar_term' env body  in
                            ([], [[]], uu____3191)  in
                          FStar_Parser_AST.QExists uu____3178  in
                        mk1 uu____3177)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3218)::[] -> resugar b
                  | uu____3235 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3245) ->
               let uu____3250 = FStar_List.hd args1  in
               (match uu____3250 with
                | (e1,uu____3264) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3333  ->
                         match uu____3333 with
                         | (e1,qual) ->
                             let uu____3350 = resugar_term' env e1  in
                             let uu____3351 = resugar_imp qual  in
                             (uu____3350, uu____3351)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3364 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3364 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3412 =
                               let uu____3413 =
                                 let uu____3420 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3420)  in
                               FStar_Parser_AST.Op uu____3413  in
                             mk1 uu____3412  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3438  ->
                                  match uu____3438 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3453 =
                      let uu____3454 =
                        let uu____3461 =
                          let uu____3464 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3464
                           in
                        (op1, uu____3461)  in
                      FStar_Parser_AST.Op uu____3454  in
                    mk1 uu____3453
                | uu____3477 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3546 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3546 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3592 =
                   let uu____3605 =
                     let uu____3610 = resugar_pat' env pat1 branch_bv  in
                     let uu____3611 = resugar_term' env e  in
                     (uu____3610, uu____3611)  in
                   (FStar_Pervasives_Native.None, uu____3605)  in
                 [uu____3592]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3663,t1)::(pat2,uu____3666,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3762 =
            let uu____3763 =
              let uu____3770 = resugar_term' env e  in
              let uu____3771 = resugar_term' env t1  in
              let uu____3772 = resugar_term' env t2  in
              (uu____3770, uu____3771, uu____3772)  in
            FStar_Parser_AST.If uu____3763  in
          mk1 uu____3762
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3838 =
            match uu____3838 with
            | (pat,wopt,b) ->
                let uu____3880 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3880 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3932 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3932
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3936 =
            let uu____3937 =
              let uu____3952 = resugar_term' env e  in
              let uu____3953 = FStar_List.map resugar_branch branches  in
              (uu____3952, uu____3953)  in
            FStar_Parser_AST.Match uu____3937  in
          mk1 uu____3936
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3999) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4068 =
            let uu____4069 =
              let uu____4078 = resugar_term' env e  in
              (uu____4078, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4069  in
          mk1 uu____4068
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4104 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4104 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4157 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4157
                    in
                 let uu____4164 =
                   let uu____4169 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4169
                    in
                 match uu____4164 with
                 | (univs1,td) ->
                     let uu____4188 =
                       let uu____4195 =
                         let uu____4196 = FStar_Syntax_Subst.compress td  in
                         uu____4196.FStar_Syntax_Syntax.n  in
                       match uu____4195 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4205,(t1,uu____4207)::(d,uu____4209)::[])
                           -> (t1, d)
                       | uu____4250 -> failwith "wrong let binding format"
                        in
                     (match uu____4188 with
                      | (typ,def) ->
                          let uu____4279 =
                            let uu____4294 =
                              let uu____4295 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4295.FStar_Syntax_Syntax.n  in
                            match uu____4294 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4314) ->
                                let uu____4335 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4335 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4365 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4365
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4383 -> ([], def, false)  in
                          (match uu____4279 with
                           | (binders,term,is_pat_app) ->
                               let uu____4433 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4444 =
                                       let uu____4445 =
                                         let uu____4446 =
                                           let uu____4453 =
                                             bv_as_unique_ident bv  in
                                           (uu____4453,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4446
                                          in
                                       mk_pat uu____4445  in
                                     (uu____4444, term)
                                  in
                               (match uu____4433 with
                                | (pat,term1) ->
                                    let uu____4474 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4514  ->
                                                  match uu____4514 with
                                                  | (bv,q) ->
                                                      let uu____4529 =
                                                        resugar_arg_qual q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4529
                                                        (fun q1  ->
                                                           let uu____4541 =
                                                             let uu____4542 =
                                                               let uu____4549
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4549,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4542
                                                              in
                                                           mk_pat uu____4541)))
                                           in
                                        let uu____4552 =
                                          let uu____4557 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4557)
                                           in
                                        let uu____4560 =
                                          universe_to_string univs1  in
                                        (uu____4552, uu____4560)
                                      else
                                        (let uu____4566 =
                                           let uu____4571 =
                                             resugar_term' env term1  in
                                           (pat, uu____4571)  in
                                         let uu____4572 =
                                           universe_to_string univs1  in
                                         (uu____4566, uu____4572))
                                       in
                                    (attrs_opt, uu____4474))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4672 =
                   match uu____4672 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4728 =
                         let uu____4729 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4729  in
                       if uu____4728
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4804) ->
          let s =
            let uu____4822 =
              let uu____4823 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____4823 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4822  in
          let uu____4824 = mk1 FStar_Parser_AST.Wild  in label s uu____4824
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____4832 =
            let uu____4833 =
              let uu____4838 = resugar_term' env tm  in (uu____4838, qi1)  in
            FStar_Parser_AST.Quote uu____4833  in
          mk1 uu____4832
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___192_4850 =
            match uu___192_4850 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4858,(uu____4859,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____4920 =
                        let uu____4921 =
                          let uu____4930 = resugar_seq t11  in
                          (uu____4930, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____4921  in
                      mk1 uu____4920
                  | uu____4933 -> t1  in
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
                 | uu____4979 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval  ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                let uu____4981 =
                  let uu____4982 = FStar_Syntax_Subst.compress e  in
                  uu____4982.FStar_Syntax_Syntax.n  in
                (match uu____4981 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____4986;
                        FStar_Syntax_Syntax.vars = uu____4987;_},(term,uu____4989)::[])
                     -> resugar_term' env term
                 | uu____5018 -> failwith "mutable_rval should have app term")
             in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5054  ->
                         match uu____5054 with
                         | (x,uu____5060) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l,uu____5062,p) ->
               let uu____5064 =
                 let uu____5065 =
                   let uu____5072 = resugar_term' env e  in
                   (uu____5072, l, p)  in
                 FStar_Parser_AST.Labeled uu____5065  in
               mk1 uu____5064
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____5081 =
                 let uu____5082 =
                   let uu____5091 = resugar_term' env e  in
                   let uu____5092 =
                     let uu____5093 =
                       let uu____5094 =
                         let uu____5105 =
                           let uu____5112 =
                             let uu____5117 = resugar_term' env t1  in
                             (uu____5117, FStar_Parser_AST.Nothing)  in
                           [uu____5112]  in
                         (name1, uu____5105)  in
                       FStar_Parser_AST.Construct uu____5094  in
                     mk1 uu____5093  in
                   (uu____5091, uu____5092, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5082  in
               mk1 uu____5081
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5135,t1) ->
               let uu____5141 =
                 let uu____5142 =
                   let uu____5151 = resugar_term' env e  in
                   let uu____5152 =
                     let uu____5153 =
                       let uu____5154 =
                         let uu____5165 =
                           let uu____5172 =
                             let uu____5177 = resugar_term' env t1  in
                             (uu____5177, FStar_Parser_AST.Nothing)  in
                           [uu____5172]  in
                         (name1, uu____5165)  in
                       FStar_Parser_AST.Construct uu____5154  in
                     mk1 uu____5153  in
                   (uu____5151, uu____5152, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5142  in
               mk1 uu____5141)
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
               let uu____5228 = FStar_Options.print_universes ()  in
               if uu____5228
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
               let uu____5289 = FStar_Options.print_universes ()  in
               if uu____5289
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
            let uu____5330 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5330, FStar_Parser_AST.Nothing)  in
          let uu____5331 = FStar_Options.print_effect_args ()  in
          if uu____5331
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____5350 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____5350
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5413 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5413, (FStar_Pervasives_Native.snd post))  in
                    let uu____5418 =
                      let uu____5425 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5425 then [] else [pre]  in
                    let uu____5447 =
                      let uu____5454 =
                        let uu____5461 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5461 then [] else [pats]  in
                      FStar_List.append [post1] uu____5454  in
                    FStar_List.append uu____5418 uu____5447
                | uu____5499 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5528  ->
                   match uu____5528 with
                   | (e,uu____5538) ->
                       let uu____5539 = resugar_term' env e  in
                       (uu____5539, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___193_5564 =
              match uu___193_5564 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5597 = resugar_term' env e  in
                         (uu____5597, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5602 -> aux l tl1)
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
        let uu____5648 = b  in
        match uu____5648 with
        | (x,aq) ->
            let uu____5653 = resugar_arg_qual aq  in
            FStar_Util.map_opt uu____5653
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5667 =
                       let uu____5668 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5668  in
                     FStar_Parser_AST.mk_binder uu____5667 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5669 ->
                     let uu____5670 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5670
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5672 =
                          let uu____5673 =
                            let uu____5678 = bv_as_unique_ident x  in
                            (uu____5678, e)  in
                          FStar_Parser_AST.Annotated uu____5673  in
                        FStar_Parser_AST.mk_binder uu____5672 r
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
              let uu____5698 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5698  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5701 =
                if used
                then
                  let uu____5702 =
                    let uu____5709 = bv_as_unique_ident v1  in
                    (uu____5709, aqual)  in
                  FStar_Parser_AST.PatVar uu____5702
                else FStar_Parser_AST.PatWild  in
              mk1 uu____5701  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5715;
                  FStar_Syntax_Syntax.vars = uu____5716;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5726 = FStar_Options.print_bound_var_types ()  in
                if uu____5726
                then
                  let uu____5727 =
                    let uu____5728 =
                      let uu____5739 =
                        let uu____5746 = resugar_term' env typ  in
                        (uu____5746, FStar_Pervasives_Native.None)  in
                      (pat, uu____5739)  in
                    FStar_Parser_AST.PatAscribed uu____5728  in
                  mk1 uu____5727
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
          let uu____5764 = resugar_arg_qual qual  in
          FStar_Util.map_opt uu____5764
            (fun aqual  ->
               let uu____5776 =
                 let uu____5781 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                   uu____5781
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5776)

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
          (let uu____5844 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5844) &&
            (let uu____5846 =
               FStar_List.existsML
                 (fun uu____5857  ->
                    match uu____5857 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5873)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5878 -> false
                          | uu____5879 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5846)
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
            let uu____5942 = may_drop_implicits args  in
            if uu____5942 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____5962  ->
                 match uu____5962 with
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
              ((let uu____6008 =
                  let uu____6009 =
                    let uu____6010 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6010  in
                  Prims.op_Negation uu____6009  in
                if uu____6008
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
              let uu____6046 = filter_pattern_imp args  in
              (match uu____6046 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____6086 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____6086 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6102 =
                       let uu____6107 =
                         let uu____6108 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6108
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6107)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6102);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____6151  ->
                        match uu____6151 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____6163 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____6163)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____6167;
                 FStar_Syntax_Syntax.fv_delta = uu____6168;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____6195 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____6195 FStar_List.rev  in
              let args1 =
                let uu____6211 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____6229  ->
                          match uu____6229 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____6211 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6303 = map21 tl1 []  in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6303
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6326 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6326
                 in
              let args2 =
                let uu____6344 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6344 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6386 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6386 with
               | FStar_Pervasives_Native.Some (op,uu____6396) ->
                   let uu____6407 =
                     let uu____6408 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____6408  in
                   mk1 uu____6407
               | FStar_Pervasives_Native.None  ->
                   let uu____6415 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6415 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6420 ->
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
  fun uu___194_6435  ->
    match uu___194_6435 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6444 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6445 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6446 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6451 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6460 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6469 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___195_6474  ->
    match uu___195_6474 with
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
            (tylid,uvs,bs,t,uu____6510,datacons) ->
            let uu____6520 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6547,uu____6548,uu____6549,inductive_lid,uu____6551,uu____6552)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6557 -> failwith "unexpected"))
               in
            (match uu____6520 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6576 = FStar_Options.print_implicits ()  in
                   if uu____6576 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6590 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___196_6595  ->
                             match uu___196_6595 with
                             | FStar_Syntax_Syntax.RecordType uu____6596 ->
                                 true
                             | uu____6605 -> false))
                      in
                   if uu____6590
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6657,univs1,term,uu____6660,num,uu____6662)
                           ->
                           let uu____6667 =
                             let uu____6668 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6668.FStar_Syntax_Syntax.n  in
                           (match uu____6667 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6682)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6743  ->
                                          match uu____6743 with
                                          | (b,qual) ->
                                              let uu____6758 =
                                                let uu____6759 =
                                                  bv_as_unique_ident b  in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6759
                                                 in
                                              let uu____6760 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6758, uu____6760,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6771 -> failwith "unexpected")
                       | uu____6782 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____6907,num,uu____6909) ->
                            let c =
                              let uu____6927 =
                                let uu____6930 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____6930  in
                              ((l.FStar_Ident.ident), uu____6927,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____6947 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____7021 ->
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
        let uu____7045 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____7045;
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
        let uu____7071 = ts  in
        match uu____7071 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____7083 =
              let uu____7084 =
                let uu____7097 =
                  let uu____7106 =
                    let uu____7113 =
                      let uu____7114 =
                        let uu____7127 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____7127)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____7114  in
                    (uu____7113, FStar_Pervasives_Native.None)  in
                  [uu____7106]  in
                (false, uu____7097)  in
              FStar_Parser_AST.Tycon uu____7084  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____7083
  
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
              let uu____7205 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____7205 with
              | (bs,action_defn) ->
                  let uu____7212 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____7212 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____7222 = FStar_Options.print_implicits ()
                            in
                         if uu____7222
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____7229 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____7229 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____7245 =
                             let uu____7256 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____7256,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____7245  in
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
            let uu____7330 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7330 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7340 = FStar_Options.print_implicits ()  in
                  if uu____7340 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7347 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7347 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7415) ->
          let uu____7424 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7446 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7463 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7470 -> false
                    | uu____7485 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7424 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7521 se1 =
                 match uu____7521 with
                 | (datacon_ses1,tycons) ->
                     let uu____7547 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7547 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7562 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7562 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7597 =
                           let uu____7598 =
                             let uu____7599 =
                               let uu____7612 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, uu____7612)  in
                             FStar_Parser_AST.Tycon uu____7599  in
                           decl'_to_decl se uu____7598  in
                         FStar_Pervasives_Native.Some uu____7597
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7643,uu____7644,uu____7645,uu____7646,uu____7647)
                              ->
                              let uu____7652 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7652
                          | uu____7655 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7658 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7664) ->
          let uu____7669 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___197_7675  ->
                    match uu___197_7675 with
                    | FStar_Syntax_Syntax.Projector (uu____7676,uu____7677)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7678 -> true
                    | uu____7679 -> false))
             in
          if uu____7669
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7710) ->
                 let uu____7739 =
                   let uu____7740 =
                     let uu____7741 =
                       let uu____7752 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7752)  in
                     FStar_Parser_AST.TopLevelLet uu____7741  in
                   decl'_to_decl se uu____7740  in
                 FStar_Pervasives_Native.Some uu____7739
             | uu____7789 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7793,fml) ->
          let uu____7795 =
            let uu____7796 =
              let uu____7797 =
                let uu____7802 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7802)  in
              FStar_Parser_AST.Assume uu____7797  in
            decl'_to_decl se uu____7796  in
          FStar_Pervasives_Native.Some uu____7795
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7804 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7804
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7806 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7806
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7815,t) ->
                let uu____7825 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7825
            | uu____7826 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7834,t) ->
                let uu____7844 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7844
            | uu____7845 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7869 -> failwith "Should not happen hopefully"  in
          let uu____7878 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____7878
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____7888 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7888 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____7900 = FStar_Options.print_implicits ()  in
                 if uu____7900 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____7913 =
                 let uu____7914 =
                   let uu____7915 =
                     let uu____7928 =
                       let uu____7937 =
                         let uu____7944 =
                           let uu____7945 =
                             let uu____7958 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____7958)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____7945  in
                         (uu____7944, FStar_Pervasives_Native.None)  in
                       [uu____7937]  in
                     (false, uu____7928)  in
                   FStar_Parser_AST.Tycon uu____7915  in
                 decl'_to_decl se uu____7914  in
               FStar_Pervasives_Native.Some uu____7913)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____7986 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____7986
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____7990 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___198_7996  ->
                    match uu___198_7996 with
                    | FStar_Syntax_Syntax.Projector (uu____7997,uu____7998)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7999 -> true
                    | uu____8000 -> false))
             in
          if uu____7990
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____8005 =
                 (let uu____8008 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____8008) || (FStar_List.isEmpty uvs)
                  in
               if uu____8005
               then resugar_term' env t
               else
                 (let uu____8010 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____8010 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____8018 = resugar_term' env t1  in
                      label universes uu____8018)
                in
             let uu____8019 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____8019)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____8026 =
            let uu____8027 =
              let uu____8028 =
                let uu____8035 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____8040 = resugar_term' env t  in
                (uu____8035, uu____8040)  in
              FStar_Parser_AST.Splice uu____8028  in
            decl'_to_decl se uu____8027  in
          FStar_Pervasives_Native.Some uu____8026
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8043 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____8060 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____8075 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) = FStar_Syntax_DsEnv.empty_env () 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____8096 = noenv resugar_term'  in uu____8096 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____8113 = noenv resugar_sigelt'  in uu____8113 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____8130 = noenv resugar_comp'  in uu____8130 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____8152 = noenv resugar_pat'  in uu____8152 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____8185 = noenv resugar_binder'  in uu____8185 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____8209 = noenv resugar_tscheme'  in uu____8209 ts 
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
          let uu____8241 = noenv resugar_eff_decl'  in
          uu____8241 for_free r q ed
  