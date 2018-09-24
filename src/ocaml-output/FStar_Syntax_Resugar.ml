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
         (fun uu___196_112  ->
            match uu___196_112 with
            | (uu____119,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____125,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____126)) -> false
            | (uu____129,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____130)) -> false
            | uu____135 -> true))
  
let filter_pattern_imp :
  'Auu____146 .
    ('Auu____146,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____146,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____177  ->
         match uu____177 with
         | (uu____182,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____214 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____224 = FStar_Options.print_universes ()  in
    if uu____224
    then
      let uu____225 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____225 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____279 ->
          let uu____280 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____280 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____287 =
                      let uu____288 =
                        let uu____289 =
                          let uu____300 = FStar_Util.string_of_int n1  in
                          (uu____300, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____289  in
                      FStar_Parser_AST.Const uu____288  in
                    mk1 uu____287 r
                | uu____311 ->
                    let e1 =
                      let uu____313 =
                        let uu____314 =
                          let uu____315 =
                            let uu____326 = FStar_Util.string_of_int n1  in
                            (uu____326, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____315  in
                        FStar_Parser_AST.Const uu____314  in
                      mk1 uu____313 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____338 =
                      let uu____339 =
                        let uu____346 = FStar_Ident.id_of_text "+"  in
                        (uu____346, [e1; e2])  in
                      FStar_Parser_AST.Op uu____339  in
                    mk1 uu____338 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____352 ->
               let t =
                 let uu____356 =
                   let uu____357 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____357  in
                 mk1 uu____356 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____363 =
                        let uu____364 =
                          let uu____371 = resugar_universe x r  in
                          (acc, uu____371, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____364  in
                      mk1 uu____363 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____373 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____384 =
              let uu____389 =
                let uu____390 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____390  in
              (uu____389, r)  in
            FStar_Ident.mk_ident uu____384  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string,Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___197_417 =
      match uu___197_417 with
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
      | uu____594 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____641 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____653 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____653 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____663 ->
               let op =
                 let uu____667 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____709) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____667
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
      let uu____917 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____917 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____971 ->
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
                (let uu____1042 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1042
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1066 =
      let uu____1067 = FStar_Syntax_Subst.compress t  in
      uu____1067.FStar_Syntax_Syntax.n  in
    match uu____1066 with
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
        let uu____1090 = string_to_op s  in
        (match uu____1090 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1122 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1137 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1147 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1153 -> true
    | uu____1154 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1165 ->
        let uu____1166 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1166
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1178 = may_shorten lid  in
      if uu____1178 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1317 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1317  in
      let uu____1318 =
        let uu____1319 = FStar_Syntax_Subst.compress t  in
        uu____1319.FStar_Syntax_Syntax.n  in
      match uu____1318 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1322 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1346 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1346
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1349 =
              let uu____1352 = bv_as_unique_ident x  in [uu____1352]  in
            FStar_Ident.lid_of_ids uu____1349  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1355 =
              let uu____1358 = bv_as_unique_ident x  in [uu____1358]  in
            FStar_Ident.lid_of_ids uu____1355  in
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
            let uu____1376 =
              let uu____1377 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1377  in
            mk1 uu____1376
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
               | uu____1387 -> failwith "wrong projector format")
            else
              (let uu____1391 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1394 =
                      let uu____1396 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1396  in
                    let uu____1398 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1394 <> uu____1398)
                  in
               if uu____1391
               then
                 let uu____1401 =
                   let uu____1402 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1402  in
                 mk1 uu____1401
               else
                 (let uu____1404 =
                    let uu____1405 =
                      let uu____1416 = maybe_shorten_fv env fv  in
                      (uu____1416, [])  in
                    FStar_Parser_AST.Construct uu____1405  in
                  mk1 uu____1404))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1434 = FStar_Options.print_universes ()  in
          if uu____1434
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
                   let uu____1463 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1463  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1486 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1493 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1493
          then
            let uu____1494 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1494
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1497 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1506 -> ("Type", true)  in
          (match uu____1497 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1510 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1510  in
               let uu____1511 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1511
               then
                 let uu____1512 =
                   let uu____1513 =
                     let uu____1520 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1520, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1513  in
                 mk1 uu____1512
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1524) ->
          let uu____1549 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1549 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1565 = FStar_Options.print_implicits ()  in
                 if uu____1565 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1600  ->
                         match uu____1600 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____1640 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1640 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1650 = FStar_Options.print_implicits ()  in
                 if uu____1650 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1658 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1658 FStar_List.rev  in
               let rec aux body3 uu___198_1683 =
                 match uu___198_1683 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1699 =
            let uu____1704 =
              let uu____1705 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1705]  in
            FStar_Syntax_Subst.open_term uu____1704 phi  in
          (match uu____1699 with
           | (x1,phi1) ->
               let b =
                 let uu____1727 =
                   let uu____1730 = FStar_List.hd x1  in
                   resugar_binder' env uu____1730 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1727  in
               let uu____1737 =
                 let uu____1738 =
                   let uu____1743 = resugar_term' env phi1  in
                   (b, uu____1743)  in
                 FStar_Parser_AST.Refine uu____1738  in
               mk1 uu____1737)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1745;
             FStar_Syntax_Syntax.vars = uu____1746;_},(e,uu____1748)::[])
          when
          (let uu____1789 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1789) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___199_1837 =
            match uu___199_1837 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1907 -> failwith "last of an empty list"  in
          let rec last_two uu___200_1945 =
            match uu___200_1945 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1976::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2053::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2124  ->
                   match uu____2124 with
                   | (e2,qual) ->
                       let uu____2141 = resugar_term' env e2  in
                       let uu____2142 = resugar_imp env qual  in
                       (uu____2141, uu____2142)) args1
               in
            let uu____2143 = resugar_term' env e1  in
            match uu____2143 with
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
                     fun uu____2180  ->
                       match uu____2180 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2196 = FStar_Options.print_implicits ()  in
            if uu____2196 then args else filter_imp args  in
          let uu____2208 = resugar_term_as_op e  in
          (match uu____2208 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2219) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2241  ->
                        match uu____2241 with
                        | (x,uu____2253) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some tail1 ->
                                 let uu____2262 =
                                   let uu____2263 =
                                     let uu____2264 =
                                       let uu____2271 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2271, [x1; tail1])  in
                                     FStar_Parser_AST.Op uu____2264  in
                                   mk1 uu____2263  in
                                 FStar_Pervasives_Native.Some uu____2262))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2274) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2296)::[] -> b
                 | uu____2313 -> failwith "wrong arguments to dtuple"  in
               let uu____2322 =
                 let uu____2323 = FStar_Syntax_Subst.compress body  in
                 uu____2323.FStar_Syntax_Syntax.n  in
               (match uu____2322 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2328) ->
                    let uu____2353 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2353 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2363 = FStar_Options.print_implicits ()
                              in
                           if uu____2363 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____2377 =
                           let uu____2378 =
                             let uu____2389 =
                               FStar_List.map
                                 (fun _0_1  -> FStar_Util.Inl _0_1) xs3
                                in
                             (uu____2389, body3)  in
                           FStar_Parser_AST.Sum uu____2378  in
                         mk1 uu____2377)
                | uu____2406 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2429  ->
                              match uu____2429 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2447) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2453) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2458 = FStar_List.hd args1  in
               (match uu____2458 with
                | (t1,uu____2472) ->
                    let uu____2477 =
                      let uu____2478 = FStar_Syntax_Subst.compress t1  in
                      uu____2478.FStar_Syntax_Syntax.n  in
                    (match uu____2477 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2483 =
                           let uu____2484 =
                             let uu____2489 = resugar_term' env t1  in
                             (uu____2489, f)  in
                           FStar_Parser_AST.Project uu____2484  in
                         mk1 uu____2483
                     | uu____2490 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2491) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2511 =
                 match new_args with
                 | (a1,uu____2521)::(a2,uu____2523)::[] -> (a1, a2)
                 | uu____2550 -> failwith "wrong arguments to try_with"  in
               (match uu____2511 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2571 =
                        let uu____2572 = FStar_Syntax_Subst.compress term  in
                        uu____2572.FStar_Syntax_Syntax.n  in
                      match uu____2571 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2577) ->
                          let uu____2602 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2602 with | (x1,e2) -> e2)
                      | uu____2609 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2611 = decomp body  in
                      resugar_term' env uu____2611  in
                    let handler1 =
                      let uu____2613 = decomp handler  in
                      resugar_term' env uu____2613  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2621,uu____2622,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2654,uu____2655,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2692 =
                            let uu____2693 =
                              let uu____2702 = resugar_body t11  in
                              (uu____2702, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2693  in
                          mk1 uu____2692
                      | uu____2705 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2762 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2792) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2798) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2804) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2895 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2908 =
                   let uu____2909 = FStar_Syntax_Subst.compress body  in
                   uu____2909.FStar_Syntax_Syntax.n  in
                 match uu____2908 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2914) ->
                     let uu____2939 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2939 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2949 = FStar_Options.print_implicits ()
                               in
                            if uu____2949 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2962 =
                            let uu____2971 =
                              let uu____2972 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2972.FStar_Syntax_Syntax.n  in
                            match uu____2971 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____2990 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____3020 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3064  ->
                                                     match uu____3064 with
                                                     | (e2,uu____3072) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3020, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3084 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3084)
                                  | uu____3091 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____2990 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3122 ->
                                let uu____3123 = resugar_term' env body2  in
                                ([], uu____3123)
                             in
                          (match uu____2962 with
                           | (pats,body3) ->
                               let uu____3140 = uncurry xs3 pats body3  in
                               (match uu____3140 with
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
                 | uu____3188 ->
                     if op = "forall"
                     then
                       let uu____3189 =
                         let uu____3190 =
                           let uu____3203 = resugar_term' env body  in
                           ([], [[]], uu____3203)  in
                         FStar_Parser_AST.QForall uu____3190  in
                       mk1 uu____3189
                     else
                       (let uu____3215 =
                          let uu____3216 =
                            let uu____3229 = resugar_term' env body  in
                            ([], [[]], uu____3229)  in
                          FStar_Parser_AST.QExists uu____3216  in
                        mk1 uu____3215)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3256)::[] -> resugar b
                  | uu____3273 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3283) ->
               let uu____3288 = FStar_List.hd args1  in
               (match uu____3288 with
                | (e1,uu____3302) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3371  ->
                         match uu____3371 with
                         | (e1,qual) ->
                             let uu____3388 = resugar_term' env e1  in
                             let uu____3389 = resugar_imp env qual  in
                             (uu____3388, uu____3389)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3402 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3402 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3450 =
                               let uu____3451 =
                                 let uu____3458 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3458)  in
                               FStar_Parser_AST.Op uu____3451  in
                             mk1 uu____3450  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3476  ->
                                  match uu____3476 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3491 =
                      let uu____3492 =
                        let uu____3499 =
                          let uu____3502 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3502
                           in
                        (op1, uu____3499)  in
                      FStar_Parser_AST.Op uu____3492  in
                    mk1 uu____3491
                | uu____3515 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3584 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3584 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3630 =
                   let uu____3643 =
                     let uu____3648 = resugar_pat' env pat1 branch_bv  in
                     let uu____3649 = resugar_term' env e  in
                     (uu____3648, uu____3649)  in
                   (FStar_Pervasives_Native.None, uu____3643)  in
                 [uu____3630]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3701,t1)::(pat2,uu____3704,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3800 =
            let uu____3801 =
              let uu____3808 = resugar_term' env e  in
              let uu____3809 = resugar_term' env t1  in
              let uu____3810 = resugar_term' env t2  in
              (uu____3808, uu____3809, uu____3810)  in
            FStar_Parser_AST.If uu____3801  in
          mk1 uu____3800
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3876 =
            match uu____3876 with
            | (pat,wopt,b) ->
                let uu____3918 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3918 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3970 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3970
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3974 =
            let uu____3975 =
              let uu____3990 = resugar_term' env e  in
              let uu____3991 = FStar_List.map resugar_branch branches  in
              (uu____3990, uu____3991)  in
            FStar_Parser_AST.Match uu____3975  in
          mk1 uu____3974
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4037) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4106 =
            let uu____4107 =
              let uu____4116 = resugar_term' env e  in
              (uu____4116, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4107  in
          mk1 uu____4106
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4142 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4142 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4195 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4195
                    in
                 let uu____4202 =
                   let uu____4207 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4207
                    in
                 match uu____4202 with
                 | (univs1,td) ->
                     let uu____4226 =
                       let uu____4233 =
                         let uu____4234 = FStar_Syntax_Subst.compress td  in
                         uu____4234.FStar_Syntax_Syntax.n  in
                       match uu____4233 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4243,(t1,uu____4245)::(d,uu____4247)::[])
                           -> (t1, d)
                       | uu____4304 -> failwith "wrong let binding format"
                        in
                     (match uu____4226 with
                      | (typ,def) ->
                          let uu____4333 =
                            let uu____4348 =
                              let uu____4349 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4349.FStar_Syntax_Syntax.n  in
                            match uu____4348 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4368) ->
                                let uu____4393 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4393 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4423 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4423
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4441 -> ([], def, false)  in
                          (match uu____4333 with
                           | (binders,term,is_pat_app) ->
                               let uu____4491 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4502 =
                                       let uu____4503 =
                                         let uu____4504 =
                                           let uu____4511 =
                                             bv_as_unique_ident bv  in
                                           (uu____4511,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4504
                                          in
                                       mk_pat uu____4503  in
                                     (uu____4502, term)
                                  in
                               (match uu____4491 with
                                | (pat,term1) ->
                                    let uu____4532 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4572  ->
                                                  match uu____4572 with
                                                  | (bv,q) ->
                                                      let uu____4587 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4587
                                                        (fun q1  ->
                                                           let uu____4599 =
                                                             let uu____4600 =
                                                               let uu____4607
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4607,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4600
                                                              in
                                                           mk_pat uu____4599)))
                                           in
                                        let uu____4610 =
                                          let uu____4615 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4615)
                                           in
                                        let uu____4618 =
                                          universe_to_string univs1  in
                                        (uu____4610, uu____4618)
                                      else
                                        (let uu____4624 =
                                           let uu____4629 =
                                             resugar_term' env term1  in
                                           (pat, uu____4629)  in
                                         let uu____4630 =
                                           universe_to_string univs1  in
                                         (uu____4624, uu____4630))
                                       in
                                    (attrs_opt, uu____4532))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4730 =
                   match uu____4730 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4786 =
                         let uu____4787 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4787  in
                       if uu____4786
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4862) ->
          let s =
            let uu____4880 =
              let uu____4881 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____4881 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4880  in
          let uu____4882 = mk1 FStar_Parser_AST.Wild  in label s uu____4882
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____4890 =
            let uu____4891 =
              let uu____4896 = resugar_term' env tm  in (uu____4896, qi1)  in
            FStar_Parser_AST.Quote uu____4891  in
          mk1 uu____4890
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___201_4908 =
            match uu___201_4908 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4916,(uu____4917,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____4978 =
                        let uu____4979 =
                          let uu____4988 = resugar_seq t11  in
                          (uu____4988, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____4979  in
                      mk1 uu____4978
                  | uu____4991 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5035  ->
                         match uu____5035 with
                         | (x,uu____5043) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____5048 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____5063 =
                 let uu____5064 =
                   let uu____5073 = resugar_term' env e  in
                   let uu____5074 =
                     let uu____5075 =
                       let uu____5076 =
                         let uu____5087 =
                           let uu____5094 =
                             let uu____5099 = resugar_term' env t1  in
                             (uu____5099, FStar_Parser_AST.Nothing)  in
                           [uu____5094]  in
                         (name1, uu____5087)  in
                       FStar_Parser_AST.Construct uu____5076  in
                     mk1 uu____5075  in
                   (uu____5073, uu____5074, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5064  in
               mk1 uu____5063
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5117,t1) ->
               let uu____5123 =
                 let uu____5124 =
                   let uu____5133 = resugar_term' env e  in
                   let uu____5134 =
                     let uu____5135 =
                       let uu____5136 =
                         let uu____5147 =
                           let uu____5154 =
                             let uu____5159 = resugar_term' env t1  in
                             (uu____5159, FStar_Parser_AST.Nothing)  in
                           [uu____5154]  in
                         (name1, uu____5147)  in
                       FStar_Parser_AST.Construct uu____5136  in
                     mk1 uu____5135  in
                   (uu____5133, uu____5134, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5124  in
               mk1 uu____5123)
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
               let uu____5210 = FStar_Options.print_universes ()  in
               if uu____5210
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
               let uu____5271 = FStar_Options.print_universes ()  in
               if uu____5271
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
            let uu____5312 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5312, FStar_Parser_AST.Nothing)  in
          let uu____5313 = FStar_Options.print_effect_args ()  in
          if uu____5313
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____5334 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____5334
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5417 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5417, (FStar_Pervasives_Native.snd post))  in
                    let uu____5428 =
                      let uu____5437 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5437 then [] else [pre]  in
                    let uu____5469 =
                      let uu____5478 =
                        let uu____5487 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5487 then [] else [pats]  in
                      FStar_List.append [post1] uu____5478  in
                    FStar_List.append uu____5428 uu____5469
                | uu____5543 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5576  ->
                   match uu____5576 with
                   | (e,uu____5588) ->
                       let uu____5593 = resugar_term' env e  in
                       (uu____5593, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___202_5618 =
              match uu___202_5618 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5651 = resugar_term' env e  in
                         (uu____5651, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5656 -> aux l tl1)
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
        let uu____5702 = b  in
        match uu____5702 with
        | (x,aq) ->
            let uu____5711 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____5711
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5725 =
                       let uu____5726 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5726  in
                     FStar_Parser_AST.mk_binder uu____5725 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5727 ->
                     let uu____5728 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5728
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5730 =
                          let uu____5731 =
                            let uu____5736 = bv_as_unique_ident x  in
                            (uu____5736, e)  in
                          FStar_Parser_AST.Annotated uu____5731  in
                        FStar_Parser_AST.mk_binder uu____5730 r
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
              let uu____5756 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5756  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5759 =
                if used
                then
                  let uu____5760 =
                    let uu____5767 = bv_as_unique_ident v1  in
                    (uu____5767, aqual)  in
                  FStar_Parser_AST.PatVar uu____5760
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____5759  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5773;
                  FStar_Syntax_Syntax.vars = uu____5774;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5784 = FStar_Options.print_bound_var_types ()  in
                if uu____5784
                then
                  let uu____5785 =
                    let uu____5786 =
                      let uu____5797 =
                        let uu____5804 = resugar_term' env typ  in
                        (uu____5804, FStar_Pervasives_Native.None)  in
                      (pat, uu____5797)  in
                    FStar_Parser_AST.PatAscribed uu____5786  in
                  mk1 uu____5785
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
          let uu____5824 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____5824
            (fun aqual  ->
               let uu____5836 =
                 let uu____5841 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                   uu____5841
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5836)

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
          (let uu____5904 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5904) &&
            (let uu____5906 =
               FStar_List.existsML
                 (fun uu____5917  ->
                    match uu____5917 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5933)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5938 -> false
                          | uu____5939 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5906)
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
            let uu____6002 = may_drop_implicits args  in
            if uu____6002 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6022  ->
                 match uu____6022 with
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
              ((let uu____6068 =
                  let uu____6069 =
                    let uu____6070 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6070  in
                  Prims.op_Negation uu____6069  in
                if uu____6068
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
              let uu____6106 = filter_pattern_imp args  in
              (match uu____6106 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____6146 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____6146 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6162 =
                       let uu____6167 =
                         let uu____6168 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6168
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6167)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6162);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____6211  ->
                        match uu____6211 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____6223 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____6223)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____6227;
                 FStar_Syntax_Syntax.fv_delta = uu____6228;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____6255 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____6255 FStar_List.rev  in
              let args1 =
                let uu____6271 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____6289  ->
                          match uu____6289 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____6271 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6363 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____6363
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6386 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6386
                 in
              let args2 =
                let uu____6404 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6404 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6446 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6446 with
               | FStar_Pervasives_Native.Some (op,uu____6456) ->
                   let uu____6467 =
                     let uu____6468 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____6468  in
                   mk1 uu____6467
               | FStar_Pervasives_Native.None  ->
                   let uu____6475 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6475 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6480 ->
              let uu____6481 =
                let uu____6482 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____6482  in
              mk1 uu____6481
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
          let uu____6518 =
            let uu____6521 =
              let uu____6522 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____6522  in
            FStar_Pervasives_Native.Some uu____6521  in
          FStar_Pervasives_Native.Some uu____6518

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
          let uu____6532 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____6532

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___203_6539  ->
    match uu___203_6539 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6546 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6547 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6548 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6553 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6562 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6571 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___204_6576  ->
    match uu___204_6576 with
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
            (tylid,uvs,bs,t,uu____6615,datacons) ->
            let uu____6625 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6652,uu____6653,uu____6654,inductive_lid,uu____6656,uu____6657)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6662 -> failwith "unexpected"))
               in
            (match uu____6625 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6681 = FStar_Options.print_implicits ()  in
                   if uu____6681 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6695 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___205_6700  ->
                             match uu___205_6700 with
                             | FStar_Syntax_Syntax.RecordType uu____6701 ->
                                 true
                             | uu____6710 -> false))
                      in
                   if uu____6695
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6762,univs1,term,uu____6765,num,uu____6767)
                           ->
                           let uu____6772 =
                             let uu____6773 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6773.FStar_Syntax_Syntax.n  in
                           (match uu____6772 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6787)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6856  ->
                                          match uu____6856 with
                                          | (b,qual) ->
                                              let uu____6877 =
                                                bv_as_unique_ident b  in
                                              let uu____6878 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6877, uu____6878,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6889 -> failwith "unexpected")
                       | uu____6900 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____7025,num,uu____7027) ->
                            let c =
                              let uu____7045 =
                                let uu____7048 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____7048  in
                              ((l.FStar_Ident.ident), uu____7045,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____7065 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____7139 ->
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
        let uu____7163 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____7163;
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
        let uu____7189 = ts  in
        match uu____7189 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____7201 =
              let uu____7202 =
                let uu____7217 =
                  let uu____7226 =
                    let uu____7233 =
                      let uu____7234 =
                        let uu____7247 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____7247)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____7234  in
                    (uu____7233, FStar_Pervasives_Native.None)  in
                  [uu____7226]  in
                (false, false, uu____7217)  in
              FStar_Parser_AST.Tycon uu____7202  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____7201
  
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
              let uu____7325 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____7325 with
              | (bs,action_defn) ->
                  let uu____7332 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____7332 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____7342 = FStar_Options.print_implicits ()
                            in
                         if uu____7342
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____7349 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____7349 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____7365 =
                             let uu____7376 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____7376,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____7365  in
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
            let uu____7450 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7450 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7460 = FStar_Options.print_implicits ()  in
                  if uu____7460 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7467 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7467 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7535) ->
          let uu____7544 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7566 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7583 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7590 -> false
                    | uu____7605 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7544 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7641 se1 =
                 match uu____7641 with
                 | (datacon_ses1,tycons) ->
                     let uu____7667 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7667 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7682 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7682 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7717 =
                           let uu____7718 =
                             let uu____7719 =
                               let uu____7734 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____7734)  in
                             FStar_Parser_AST.Tycon uu____7719  in
                           decl'_to_decl se uu____7718  in
                         FStar_Pervasives_Native.Some uu____7717
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7765,uu____7766,uu____7767,uu____7768,uu____7769)
                              ->
                              let uu____7774 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7774
                          | uu____7777 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7780 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7786) ->
          let uu____7791 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___206_7797  ->
                    match uu___206_7797 with
                    | FStar_Syntax_Syntax.Projector (uu____7798,uu____7799)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7800 -> true
                    | uu____7801 -> false))
             in
          if uu____7791
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7832) ->
                 let uu____7861 =
                   let uu____7862 =
                     let uu____7863 =
                       let uu____7874 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7874)  in
                     FStar_Parser_AST.TopLevelLet uu____7863  in
                   decl'_to_decl se uu____7862  in
                 FStar_Pervasives_Native.Some uu____7861
             | uu____7911 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7915,fml) ->
          let uu____7917 =
            let uu____7918 =
              let uu____7919 =
                let uu____7924 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7924)  in
              FStar_Parser_AST.Assume uu____7919  in
            decl'_to_decl se uu____7918  in
          FStar_Pervasives_Native.Some uu____7917
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7926 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7926
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7928 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7928
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7937,t) ->
                let uu____7947 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7947
            | uu____7948 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7956,t) ->
                let uu____7966 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7966
            | uu____7967 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7991 -> failwith "Should not happen hopefully"  in
          let uu____8000 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____8000
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____8010 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8010 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____8022 = FStar_Options.print_implicits ()  in
                 if uu____8022 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____8035 =
                 let uu____8036 =
                   let uu____8037 =
                     let uu____8052 =
                       let uu____8061 =
                         let uu____8068 =
                           let uu____8069 =
                             let uu____8082 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____8082)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____8069  in
                         (uu____8068, FStar_Pervasives_Native.None)  in
                       [uu____8061]  in
                     (false, false, uu____8052)  in
                   FStar_Parser_AST.Tycon uu____8037  in
                 decl'_to_decl se uu____8036  in
               FStar_Pervasives_Native.Some uu____8035)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____8110 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____8110
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____8114 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___207_8120  ->
                    match uu___207_8120 with
                    | FStar_Syntax_Syntax.Projector (uu____8121,uu____8122)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8123 -> true
                    | uu____8124 -> false))
             in
          if uu____8114
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____8129 =
                 (let uu____8132 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____8132) || (FStar_List.isEmpty uvs)
                  in
               if uu____8129
               then resugar_term' env t
               else
                 (let uu____8134 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____8134 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____8142 = resugar_term' env t1  in
                      label universes uu____8142)
                in
             let uu____8143 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____8143)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____8150 =
            let uu____8151 =
              let uu____8152 =
                let uu____8159 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____8164 = resugar_term' env t  in
                (uu____8159, uu____8164)  in
              FStar_Parser_AST.Splice uu____8152  in
            decl'_to_decl se uu____8151  in
          FStar_Pervasives_Native.Some uu____8150
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8167 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____8184 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____8199 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____8220 = noenv resugar_term'  in uu____8220 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____8237 = noenv resugar_sigelt'  in uu____8237 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____8254 = noenv resugar_comp'  in uu____8254 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____8276 = noenv resugar_pat'  in uu____8276 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____8309 = noenv resugar_binder'  in uu____8309 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____8333 = noenv resugar_tscheme'  in uu____8333 ts 
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
          let uu____8365 = noenv resugar_eff_decl'  in
          uu____8365 for_free r q ed
  