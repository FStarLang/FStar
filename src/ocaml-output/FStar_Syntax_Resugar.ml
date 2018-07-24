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
         (fun uu___189_112  ->
            match uu___189_112 with
            | (uu____119,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____120)) -> false
            | (uu____123,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____124)) -> false
            | uu____129 -> true))
  
let filter_pattern_imp :
  'Auu____140 .
    ('Auu____140,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____140,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____171  ->
         match uu____171 with
         | (uu____176,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      (Prims.int,FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____208 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____218 = FStar_Options.print_universes ()  in
    if uu____218
    then
      let uu____219 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____219 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____273 ->
          let uu____274 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____274 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____281 =
                      let uu____282 =
                        let uu____283 =
                          let uu____294 = FStar_Util.string_of_int n1  in
                          (uu____294, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____283  in
                      FStar_Parser_AST.Const uu____282  in
                    mk1 uu____281 r
                | uu____305 ->
                    let e1 =
                      let uu____307 =
                        let uu____308 =
                          let uu____309 =
                            let uu____320 = FStar_Util.string_of_int n1  in
                            (uu____320, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____309  in
                        FStar_Parser_AST.Const uu____308  in
                      mk1 uu____307 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____332 =
                      let uu____333 =
                        let uu____340 = FStar_Ident.id_of_text "+"  in
                        (uu____340, [e1; e2])  in
                      FStar_Parser_AST.Op uu____333  in
                    mk1 uu____332 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____346 ->
               let t =
                 let uu____350 =
                   let uu____351 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____351  in
                 mk1 uu____350 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____357 =
                        let uu____358 =
                          let uu____365 = resugar_universe x r  in
                          (acc, uu____365, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____358  in
                      mk1 uu____357 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____367 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____378 =
              let uu____383 =
                let uu____384 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____384  in
              (uu____383, r)  in
            FStar_Ident.mk_ident uu____378  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string,Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___190_411 =
      match uu___190_411 with
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
      | uu____588 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____635 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____647 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____647 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____657 ->
               let op =
                 let uu____661 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____703) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____661
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
      let uu____911 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____911 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____965 ->
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
                (let uu____1036 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1036
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1060 =
      let uu____1061 = FStar_Syntax_Subst.compress t  in
      uu____1061.FStar_Syntax_Syntax.n  in
    match uu____1060 with
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
        let uu____1084 = string_to_op s  in
        (match uu____1084 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1116 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1131 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1141 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1147 -> true
    | uu____1148 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1159 ->
        let uu____1160 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1160
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1172 = may_shorten lid  in
      if uu____1172 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1311 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1311  in
      let uu____1312 =
        let uu____1313 = FStar_Syntax_Subst.compress t  in
        uu____1313.FStar_Syntax_Syntax.n  in
      match uu____1312 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1316 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1340 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1340
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1343 =
              let uu____1346 = bv_as_unique_ident x  in [uu____1346]  in
            FStar_Ident.lid_of_ids uu____1343  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1349 =
              let uu____1352 = bv_as_unique_ident x  in [uu____1352]  in
            FStar_Ident.lid_of_ids uu____1349  in
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
            let uu____1370 =
              let uu____1371 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1371  in
            mk1 uu____1370
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
               | uu____1381 -> failwith "wrong projector format")
            else
              (let uu____1385 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1388 =
                      let uu____1390 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1390  in
                    let uu____1392 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1388 <> uu____1392)
                  in
               if uu____1385
               then
                 let uu____1395 =
                   let uu____1396 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1396  in
                 mk1 uu____1395
               else
                 (let uu____1398 =
                    let uu____1399 =
                      let uu____1410 = maybe_shorten_fv env fv  in
                      (uu____1410, [])  in
                    FStar_Parser_AST.Construct uu____1399  in
                  mk1 uu____1398))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1428 = FStar_Options.print_universes ()  in
          if uu____1428
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
                   let uu____1457 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1457  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1480 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1487 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1487
          then
            let uu____1488 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1488
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1491 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1500 -> ("Type", true)  in
          (match uu____1491 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1504 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1504  in
               let uu____1505 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1505
               then
                 let uu____1506 =
                   let uu____1507 =
                     let uu____1514 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1514, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1507  in
                 mk1 uu____1506
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1518) ->
          let uu____1543 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1543 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1559 = FStar_Options.print_implicits ()  in
                 if uu____1559 then xs1 else filter_imp xs1  in
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
          let uu____1634 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1634 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1644 = FStar_Options.print_implicits ()  in
                 if uu____1644 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1652 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1652 FStar_List.rev  in
               let rec aux body3 uu___191_1677 =
                 match uu___191_1677 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1693 =
            let uu____1698 =
              let uu____1699 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1699]  in
            FStar_Syntax_Subst.open_term uu____1698 phi  in
          (match uu____1693 with
           | (x1,phi1) ->
               let b =
                 let uu____1721 =
                   let uu____1724 = FStar_List.hd x1  in
                   resugar_binder' env uu____1724 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1721  in
               let uu____1731 =
                 let uu____1732 =
                   let uu____1737 = resugar_term' env phi1  in
                   (b, uu____1737)  in
                 FStar_Parser_AST.Refine uu____1732  in
               mk1 uu____1731)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1739;
             FStar_Syntax_Syntax.vars = uu____1740;_},(e,uu____1742)::[])
          when
          (let uu____1783 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1783) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___192_1831 =
            match uu___192_1831 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1901 -> failwith "last of an empty list"  in
          let rec last_two uu___193_1939 =
            match uu___193_1939 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1970::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2047::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2118  ->
                   match uu____2118 with
                   | (e2,qual) ->
                       let uu____2135 = resugar_term' env e2  in
                       let uu____2136 = resugar_imp env qual  in
                       (uu____2135, uu____2136)) args1
               in
            let uu____2137 = resugar_term' env e1  in
            match uu____2137 with
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
                     fun uu____2174  ->
                       match uu____2174 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2190 = FStar_Options.print_implicits ()  in
            if uu____2190 then args else filter_imp args  in
          let uu____2202 = resugar_term_as_op e  in
          (match uu____2202 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2213) ->
               (match args1 with
                | (fst1,uu____2219)::(snd1,uu____2221)::rest ->
                    let e1 =
                      let uu____2252 =
                        let uu____2253 =
                          let uu____2260 = FStar_Ident.id_of_text "*"  in
                          let uu____2261 =
                            let uu____2264 = resugar_term' env fst1  in
                            let uu____2265 =
                              let uu____2268 = resugar_term' env snd1  in
                              [uu____2268]  in
                            uu____2264 :: uu____2265  in
                          (uu____2260, uu____2261)  in
                        FStar_Parser_AST.Op uu____2253  in
                      mk1 uu____2252  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2283  ->
                           match uu____2283 with
                           | (x,uu____2291) ->
                               let uu____2296 =
                                 let uu____2297 =
                                   let uu____2304 =
                                     FStar_Ident.id_of_text "*"  in
                                   let uu____2305 =
                                     let uu____2308 =
                                       let uu____2311 = resugar_term' env x
                                          in
                                       [uu____2311]  in
                                     e1 :: uu____2308  in
                                   (uu____2304, uu____2305)  in
                                 FStar_Parser_AST.Op uu____2297  in
                               mk1 uu____2296) e1 rest
                | uu____2314 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2323) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2345)::[] -> b
                 | uu____2362 -> failwith "wrong arguments to dtuple"  in
               let uu____2371 =
                 let uu____2372 = FStar_Syntax_Subst.compress body  in
                 uu____2372.FStar_Syntax_Syntax.n  in
               (match uu____2371 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2377) ->
                    let uu____2402 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2402 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2412 = FStar_Options.print_implicits ()
                              in
                           if uu____2412 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2428 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2451  ->
                              match uu____2451 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2469) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2475) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2480 = FStar_List.hd args1  in
               (match uu____2480 with
                | (t1,uu____2494) ->
                    let uu____2499 =
                      let uu____2500 = FStar_Syntax_Subst.compress t1  in
                      uu____2500.FStar_Syntax_Syntax.n  in
                    (match uu____2499 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2505 =
                           let uu____2506 =
                             let uu____2511 = resugar_term' env t1  in
                             (uu____2511, f)  in
                           FStar_Parser_AST.Project uu____2506  in
                         mk1 uu____2505
                     | uu____2512 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2513) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2533 =
                 match new_args with
                 | (a1,uu____2543)::(a2,uu____2545)::[] -> (a1, a2)
                 | uu____2572 -> failwith "wrong arguments to try_with"  in
               (match uu____2533 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2593 =
                        let uu____2594 = FStar_Syntax_Subst.compress term  in
                        uu____2594.FStar_Syntax_Syntax.n  in
                      match uu____2593 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2599) ->
                          let uu____2624 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2624 with | (x1,e2) -> e2)
                      | uu____2631 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2633 = decomp body  in
                      resugar_term' env uu____2633  in
                    let handler1 =
                      let uu____2635 = decomp handler  in
                      resugar_term' env uu____2635  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2643,uu____2644,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2676,uu____2677,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2714 =
                            let uu____2715 =
                              let uu____2724 = resugar_body t11  in
                              (uu____2724, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2715  in
                          mk1 uu____2714
                      | uu____2727 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2784 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2814) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2820) when
               (((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                  || (op = ":="))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2826) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2917 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2930 =
                   let uu____2931 = FStar_Syntax_Subst.compress body  in
                   uu____2931.FStar_Syntax_Syntax.n  in
                 match uu____2930 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2936) ->
                     let uu____2961 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2961 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2971 = FStar_Options.print_implicits ()
                               in
                            if uu____2971 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2984 =
                            let uu____2993 =
                              let uu____2994 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2994.FStar_Syntax_Syntax.n  in
                            match uu____2993 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3012 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____3042 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3086  ->
                                                     match uu____3086 with
                                                     | (e2,uu____3094) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3042, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3106 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3106)
                                  | uu____3113 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3012 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3144 ->
                                let uu____3145 = resugar_term' env body2  in
                                ([], uu____3145)
                             in
                          (match uu____2984 with
                           | (pats,body3) ->
                               let uu____3162 = uncurry xs3 pats body3  in
                               (match uu____3162 with
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
                 | uu____3210 ->
                     if op = "forall"
                     then
                       let uu____3211 =
                         let uu____3212 =
                           let uu____3225 = resugar_term' env body  in
                           ([], [[]], uu____3225)  in
                         FStar_Parser_AST.QForall uu____3212  in
                       mk1 uu____3211
                     else
                       (let uu____3237 =
                          let uu____3238 =
                            let uu____3251 = resugar_term' env body  in
                            ([], [[]], uu____3251)  in
                          FStar_Parser_AST.QExists uu____3238  in
                        mk1 uu____3237)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3278)::[] -> resugar b
                  | uu____3295 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3305) ->
               let uu____3310 = FStar_List.hd args1  in
               (match uu____3310 with
                | (e1,uu____3324) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3393  ->
                         match uu____3393 with
                         | (e1,qual) ->
                             let uu____3410 = resugar_term' env e1  in
                             let uu____3411 = resugar_imp env qual  in
                             (uu____3410, uu____3411)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3424 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3424 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3472 =
                               let uu____3473 =
                                 let uu____3480 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3480)  in
                               FStar_Parser_AST.Op uu____3473  in
                             mk1 uu____3472  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3498  ->
                                  match uu____3498 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3513 =
                      let uu____3514 =
                        let uu____3521 =
                          let uu____3524 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3524
                           in
                        (op1, uu____3521)  in
                      FStar_Parser_AST.Op uu____3514  in
                    mk1 uu____3513
                | uu____3537 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3606 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3606 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3652 =
                   let uu____3665 =
                     let uu____3670 = resugar_pat' env pat1 branch_bv  in
                     let uu____3671 = resugar_term' env e  in
                     (uu____3670, uu____3671)  in
                   (FStar_Pervasives_Native.None, uu____3665)  in
                 [uu____3652]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3723,t1)::(pat2,uu____3726,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3822 =
            let uu____3823 =
              let uu____3830 = resugar_term' env e  in
              let uu____3831 = resugar_term' env t1  in
              let uu____3832 = resugar_term' env t2  in
              (uu____3830, uu____3831, uu____3832)  in
            FStar_Parser_AST.If uu____3823  in
          mk1 uu____3822
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3898 =
            match uu____3898 with
            | (pat,wopt,b) ->
                let uu____3940 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3940 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3992 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3992
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3996 =
            let uu____3997 =
              let uu____4012 = resugar_term' env e  in
              let uu____4013 = FStar_List.map resugar_branch branches  in
              (uu____4012, uu____4013)  in
            FStar_Parser_AST.Match uu____3997  in
          mk1 uu____3996
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4059) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4128 =
            let uu____4129 =
              let uu____4138 = resugar_term' env e  in
              (uu____4138, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4129  in
          mk1 uu____4128
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4164 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4164 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4217 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4217
                    in
                 let uu____4224 =
                   let uu____4229 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4229
                    in
                 match uu____4224 with
                 | (univs1,td) ->
                     let uu____4248 =
                       let uu____4255 =
                         let uu____4256 = FStar_Syntax_Subst.compress td  in
                         uu____4256.FStar_Syntax_Syntax.n  in
                       match uu____4255 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4265,(t1,uu____4267)::(d,uu____4269)::[])
                           -> (t1, d)
                       | uu____4326 -> failwith "wrong let binding format"
                        in
                     (match uu____4248 with
                      | (typ,def) ->
                          let uu____4355 =
                            let uu____4370 =
                              let uu____4371 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4371.FStar_Syntax_Syntax.n  in
                            match uu____4370 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4390) ->
                                let uu____4415 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4415 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4445 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4445
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4463 -> ([], def, false)  in
                          (match uu____4355 with
                           | (binders,term,is_pat_app) ->
                               let uu____4513 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4524 =
                                       let uu____4525 =
                                         let uu____4526 =
                                           let uu____4533 =
                                             bv_as_unique_ident bv  in
                                           (uu____4533,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4526
                                          in
                                       mk_pat uu____4525  in
                                     (uu____4524, term)
                                  in
                               (match uu____4513 with
                                | (pat,term1) ->
                                    let uu____4554 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4594  ->
                                                  match uu____4594 with
                                                  | (bv,q) ->
                                                      let uu____4609 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4609
                                                        (fun q1  ->
                                                           let uu____4621 =
                                                             let uu____4622 =
                                                               let uu____4629
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4629,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4622
                                                              in
                                                           mk_pat uu____4621)))
                                           in
                                        let uu____4632 =
                                          let uu____4637 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4637)
                                           in
                                        let uu____4640 =
                                          universe_to_string univs1  in
                                        (uu____4632, uu____4640)
                                      else
                                        (let uu____4646 =
                                           let uu____4651 =
                                             resugar_term' env term1  in
                                           (pat, uu____4651)  in
                                         let uu____4652 =
                                           universe_to_string univs1  in
                                         (uu____4646, uu____4652))
                                       in
                                    (attrs_opt, uu____4554))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4752 =
                   match uu____4752 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4808 =
                         let uu____4809 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4809  in
                       if uu____4808
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4884) ->
          let s =
            let uu____4902 =
              let uu____4903 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____4903 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4902  in
          let uu____4904 = mk1 FStar_Parser_AST.Wild  in label s uu____4904
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____4912 =
            let uu____4913 =
              let uu____4918 = resugar_term' env tm  in (uu____4918, qi1)  in
            FStar_Parser_AST.Quote uu____4913  in
          mk1 uu____4912
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___194_4930 =
            match uu___194_4930 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4938,(uu____4939,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____5000 =
                        let uu____5001 =
                          let uu____5010 = resugar_seq t11  in
                          (uu____5010, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____5001  in
                      mk1 uu____5000
                  | uu____5013 -> t1  in
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
                 | uu____5059 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval  ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                let uu____5061 =
                  let uu____5062 = FStar_Syntax_Subst.compress e  in
                  uu____5062.FStar_Syntax_Syntax.n  in
                (match uu____5061 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____5066;
                        FStar_Syntax_Syntax.vars = uu____5067;_},(term,uu____5069)::[])
                     -> resugar_term' env term
                 | uu____5108 -> failwith "mutable_rval should have app term")
             in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5152  ->
                         match uu____5152 with
                         | (x,uu____5160) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l,uu____5166,p) ->
               let uu____5168 =
                 let uu____5169 =
                   let uu____5176 = resugar_term' env e  in
                   (uu____5176, l, p)  in
                 FStar_Parser_AST.Labeled uu____5169  in
               mk1 uu____5168
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____5185 =
                 let uu____5186 =
                   let uu____5195 = resugar_term' env e  in
                   let uu____5196 =
                     let uu____5197 =
                       let uu____5198 =
                         let uu____5209 =
                           let uu____5216 =
                             let uu____5221 = resugar_term' env t1  in
                             (uu____5221, FStar_Parser_AST.Nothing)  in
                           [uu____5216]  in
                         (name1, uu____5209)  in
                       FStar_Parser_AST.Construct uu____5198  in
                     mk1 uu____5197  in
                   (uu____5195, uu____5196, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5186  in
               mk1 uu____5185
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5239,t1) ->
               let uu____5245 =
                 let uu____5246 =
                   let uu____5255 = resugar_term' env e  in
                   let uu____5256 =
                     let uu____5257 =
                       let uu____5258 =
                         let uu____5269 =
                           let uu____5276 =
                             let uu____5281 = resugar_term' env t1  in
                             (uu____5281, FStar_Parser_AST.Nothing)  in
                           [uu____5276]  in
                         (name1, uu____5269)  in
                       FStar_Parser_AST.Construct uu____5258  in
                     mk1 uu____5257  in
                   (uu____5255, uu____5256, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5246  in
               mk1 uu____5245)
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
               let uu____5332 = FStar_Options.print_universes ()  in
               if uu____5332
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
               let uu____5393 = FStar_Options.print_universes ()  in
               if uu____5393
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
            let uu____5434 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5434, FStar_Parser_AST.Nothing)  in
          let uu____5435 = FStar_Options.print_effect_args ()  in
          if uu____5435
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____5456 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____5456
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5539 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5539, (FStar_Pervasives_Native.snd post))  in
                    let uu____5550 =
                      let uu____5559 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5559 then [] else [pre]  in
                    let uu____5591 =
                      let uu____5600 =
                        let uu____5609 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5609 then [] else [pats]  in
                      FStar_List.append [post1] uu____5600  in
                    FStar_List.append uu____5550 uu____5591
                | uu____5665 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5698  ->
                   match uu____5698 with
                   | (e,uu____5710) ->
                       let uu____5715 = resugar_term' env e  in
                       (uu____5715, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___195_5740 =
              match uu___195_5740 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5773 = resugar_term' env e  in
                         (uu____5773, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5778 -> aux l tl1)
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
        let uu____5824 = b  in
        match uu____5824 with
        | (x,aq) ->
            let uu____5833 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____5833
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5847 =
                       let uu____5848 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5848  in
                     FStar_Parser_AST.mk_binder uu____5847 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5849 ->
                     let uu____5850 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5850
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5852 =
                          let uu____5853 =
                            let uu____5858 = bv_as_unique_ident x  in
                            (uu____5858, e)  in
                          FStar_Parser_AST.Annotated uu____5853  in
                        FStar_Parser_AST.mk_binder uu____5852 r
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
              let uu____5878 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5878  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5881 =
                if used
                then
                  let uu____5882 =
                    let uu____5889 = bv_as_unique_ident v1  in
                    (uu____5889, aqual)  in
                  FStar_Parser_AST.PatVar uu____5882
                else FStar_Parser_AST.PatWild  in
              mk1 uu____5881  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5895;
                  FStar_Syntax_Syntax.vars = uu____5896;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5906 = FStar_Options.print_bound_var_types ()  in
                if uu____5906
                then
                  let uu____5907 =
                    let uu____5908 =
                      let uu____5919 =
                        let uu____5926 = resugar_term' env typ  in
                        (uu____5926, FStar_Pervasives_Native.None)  in
                      (pat, uu____5919)  in
                    FStar_Parser_AST.PatAscribed uu____5908  in
                  mk1 uu____5907
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
          let uu____5946 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____5946
            (fun aqual  ->
               let uu____5958 =
                 let uu____5963 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                   uu____5963
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5958)

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
          (let uu____6026 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6026) &&
            (let uu____6028 =
               FStar_List.existsML
                 (fun uu____6039  ->
                    match uu____6039 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6055)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6060 -> false
                          | uu____6061 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6028)
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
            let uu____6124 = may_drop_implicits args  in
            if uu____6124 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6144  ->
                 match uu____6144 with
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
              ((let uu____6190 =
                  let uu____6191 =
                    let uu____6192 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6192  in
                  Prims.op_Negation uu____6191  in
                if uu____6190
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
              let uu____6228 = filter_pattern_imp args  in
              (match uu____6228 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____6268 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____6268 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6284 =
                       let uu____6289 =
                         let uu____6290 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6290
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6289)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6284);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____6333  ->
                        match uu____6333 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____6345 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____6345)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____6349;
                 FStar_Syntax_Syntax.fv_delta = uu____6350;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____6377 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____6377 FStar_List.rev  in
              let args1 =
                let uu____6393 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____6411  ->
                          match uu____6411 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____6393 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6485 = map21 tl1 []  in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6485
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6508 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6508
                 in
              let args2 =
                let uu____6526 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6526 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6568 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6568 with
               | FStar_Pervasives_Native.Some (op,uu____6578) ->
                   let uu____6589 =
                     let uu____6590 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____6590  in
                   mk1 uu____6589
               | FStar_Pervasives_Native.None  ->
                   let uu____6597 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6597 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6602 ->
              mk1 FStar_Parser_AST.PatWild
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
          let uu____6636 =
            let uu____6639 =
              let uu____6640 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____6640  in
            FStar_Pervasives_Native.Some uu____6639  in
          FStar_Pervasives_Native.Some uu____6636

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
          let uu____6650 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____6650

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___196_6657  ->
    match uu___196_6657 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6664 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6665 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6666 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6671 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6680 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6689 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___197_6694  ->
    match uu___197_6694 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions  -> FStar_Parser_AST.PopOptions
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
            (tylid,uvs,bs,t,uu____6733,datacons) ->
            let uu____6743 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6770,uu____6771,uu____6772,inductive_lid,uu____6774,uu____6775)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6780 -> failwith "unexpected"))
               in
            (match uu____6743 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6799 = FStar_Options.print_implicits ()  in
                   if uu____6799 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6813 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___198_6818  ->
                             match uu___198_6818 with
                             | FStar_Syntax_Syntax.RecordType uu____6819 ->
                                 true
                             | uu____6828 -> false))
                      in
                   if uu____6813
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6880,univs1,term,uu____6883,num,uu____6885)
                           ->
                           let uu____6890 =
                             let uu____6891 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6891.FStar_Syntax_Syntax.n  in
                           (match uu____6890 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6905)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6974  ->
                                          match uu____6974 with
                                          | (b,qual) ->
                                              let uu____6995 =
                                                let uu____6996 =
                                                  bv_as_unique_ident b  in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6996
                                                 in
                                              let uu____6997 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6995, uu____6997,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____7008 -> failwith "unexpected")
                       | uu____7019 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____7144,num,uu____7146) ->
                            let c =
                              let uu____7164 =
                                let uu____7167 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____7167  in
                              ((l.FStar_Ident.ident), uu____7164,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____7184 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____7258 ->
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
        let uu____7282 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____7282;
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
        let uu____7308 = ts  in
        match uu____7308 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____7320 =
              let uu____7321 =
                let uu____7334 =
                  let uu____7343 =
                    let uu____7350 =
                      let uu____7351 =
                        let uu____7364 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____7364)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____7351  in
                    (uu____7350, FStar_Pervasives_Native.None)  in
                  [uu____7343]  in
                (false, uu____7334)  in
              FStar_Parser_AST.Tycon uu____7321  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____7320
  
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
              let uu____7442 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____7442 with
              | (bs,action_defn) ->
                  let uu____7449 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____7449 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____7459 = FStar_Options.print_implicits ()
                            in
                         if uu____7459
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____7466 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____7466 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____7482 =
                             let uu____7493 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____7493,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____7482  in
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
            let uu____7567 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7567 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7577 = FStar_Options.print_implicits ()  in
                  if uu____7577 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7584 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7584 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7652) ->
          let uu____7661 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7683 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7700 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7707 -> false
                    | uu____7722 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7661 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7758 se1 =
                 match uu____7758 with
                 | (datacon_ses1,tycons) ->
                     let uu____7784 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7784 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7799 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7799 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7834 =
                           let uu____7835 =
                             let uu____7836 =
                               let uu____7849 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, uu____7849)  in
                             FStar_Parser_AST.Tycon uu____7836  in
                           decl'_to_decl se uu____7835  in
                         FStar_Pervasives_Native.Some uu____7834
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7880,uu____7881,uu____7882,uu____7883,uu____7884)
                              ->
                              let uu____7889 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7889
                          | uu____7892 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7895 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7901) ->
          let uu____7906 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___199_7912  ->
                    match uu___199_7912 with
                    | FStar_Syntax_Syntax.Projector (uu____7913,uu____7914)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7915 -> true
                    | uu____7916 -> false))
             in
          if uu____7906
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7947) ->
                 let uu____7976 =
                   let uu____7977 =
                     let uu____7978 =
                       let uu____7989 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7989)  in
                     FStar_Parser_AST.TopLevelLet uu____7978  in
                   decl'_to_decl se uu____7977  in
                 FStar_Pervasives_Native.Some uu____7976
             | uu____8026 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____8030,fml) ->
          let uu____8032 =
            let uu____8033 =
              let uu____8034 =
                let uu____8039 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____8039)  in
              FStar_Parser_AST.Assume uu____8034  in
            decl'_to_decl se uu____8033  in
          FStar_Pervasives_Native.Some uu____8032
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____8041 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8041
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____8043 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____8043
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____8052,t) ->
                let uu____8070 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8070
            | uu____8071 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____8079,t) ->
                let uu____8097 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____8097
            | uu____8098 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____8122 -> failwith "Should not happen hopefully"  in
          let uu____8131 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____8131
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____8141 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8141 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____8153 = FStar_Options.print_implicits ()  in
                 if uu____8153 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____8166 =
                 let uu____8167 =
                   let uu____8168 =
                     let uu____8181 =
                       let uu____8190 =
                         let uu____8197 =
                           let uu____8198 =
                             let uu____8211 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____8211)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____8198  in
                         (uu____8197, FStar_Pervasives_Native.None)  in
                       [uu____8190]  in
                     (false, uu____8181)  in
                   FStar_Parser_AST.Tycon uu____8168  in
                 decl'_to_decl se uu____8167  in
               FStar_Pervasives_Native.Some uu____8166)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____8239 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____8239
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____8243 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___200_8249  ->
                    match uu___200_8249 with
                    | FStar_Syntax_Syntax.Projector (uu____8250,uu____8251)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8252 -> true
                    | uu____8253 -> false))
             in
          if uu____8243
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____8258 =
                 (let uu____8261 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____8261) || (FStar_List.isEmpty uvs)
                  in
               if uu____8258
               then resugar_term' env t
               else
                 (let uu____8263 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____8263 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____8271 = resugar_term' env t1  in
                      label universes uu____8271)
                in
             let uu____8272 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____8272)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____8279 =
            let uu____8280 =
              let uu____8281 =
                let uu____8288 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____8293 = resugar_term' env t  in
                (uu____8288, uu____8293)  in
              FStar_Parser_AST.Splice uu____8281  in
            decl'_to_decl se uu____8280  in
          FStar_Pervasives_Native.Some uu____8279
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8296 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____8313 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____8328 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) = FStar_Syntax_DsEnv.empty_env () 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____8349 = noenv resugar_term'  in uu____8349 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____8366 = noenv resugar_sigelt'  in uu____8366 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____8383 = noenv resugar_comp'  in uu____8383 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____8405 = noenv resugar_pat'  in uu____8405 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____8438 = noenv resugar_binder'  in uu____8438 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____8462 = noenv resugar_tscheme'  in uu____8462 ts 
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
          let uu____8494 = noenv resugar_eff_decl'  in
          uu____8494 for_free r q ed
  