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
               (match args1 with
                | (fst1,uu____2225)::(snd1,uu____2227)::rest ->
                    let e1 =
                      let uu____2258 =
                        let uu____2259 =
                          let uu____2266 = FStar_Ident.id_of_text "*"  in
                          let uu____2267 =
                            let uu____2270 = resugar_term' env fst1  in
                            let uu____2271 =
                              let uu____2274 = resugar_term' env snd1  in
                              [uu____2274]  in
                            uu____2270 :: uu____2271  in
                          (uu____2266, uu____2267)  in
                        FStar_Parser_AST.Op uu____2259  in
                      mk1 uu____2258  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2289  ->
                           match uu____2289 with
                           | (x,uu____2297) ->
                               let uu____2302 =
                                 let uu____2303 =
                                   let uu____2310 =
                                     FStar_Ident.id_of_text "*"  in
                                   let uu____2311 =
                                     let uu____2314 =
                                       let uu____2317 = resugar_term' env x
                                          in
                                       [uu____2317]  in
                                     e1 :: uu____2314  in
                                   (uu____2310, uu____2311)  in
                                 FStar_Parser_AST.Op uu____2303  in
                               mk1 uu____2302) e1 rest
                | uu____2320 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2329) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2351)::[] -> b
                 | uu____2368 -> failwith "wrong arguments to dtuple"  in
               let uu____2377 =
                 let uu____2378 = FStar_Syntax_Subst.compress body  in
                 uu____2378.FStar_Syntax_Syntax.n  in
               (match uu____2377 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2383) ->
                    let uu____2408 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2408 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2418 = FStar_Options.print_implicits ()
                              in
                           if uu____2418 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2434 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2457  ->
                              match uu____2457 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2475) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2481) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2486 = FStar_List.hd args1  in
               (match uu____2486 with
                | (t1,uu____2500) ->
                    let uu____2505 =
                      let uu____2506 = FStar_Syntax_Subst.compress t1  in
                      uu____2506.FStar_Syntax_Syntax.n  in
                    (match uu____2505 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2511 =
                           let uu____2512 =
                             let uu____2517 = resugar_term' env t1  in
                             (uu____2517, f)  in
                           FStar_Parser_AST.Project uu____2512  in
                         mk1 uu____2511
                     | uu____2518 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2519) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2539 =
                 match new_args with
                 | (a1,uu____2549)::(a2,uu____2551)::[] -> (a1, a2)
                 | uu____2578 -> failwith "wrong arguments to try_with"  in
               (match uu____2539 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2599 =
                        let uu____2600 = FStar_Syntax_Subst.compress term  in
                        uu____2600.FStar_Syntax_Syntax.n  in
                      match uu____2599 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2605) ->
                          let uu____2630 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2630 with | (x1,e2) -> e2)
                      | uu____2637 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2639 = decomp body  in
                      resugar_term' env uu____2639  in
                    let handler1 =
                      let uu____2641 = decomp handler  in
                      resugar_term' env uu____2641  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2649,uu____2650,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2682,uu____2683,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2720 =
                            let uu____2721 =
                              let uu____2730 = resugar_body t11  in
                              (uu____2730, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2721  in
                          mk1 uu____2720
                      | uu____2733 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2790 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2820) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2826) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2832) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2923 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2936 =
                   let uu____2937 = FStar_Syntax_Subst.compress body  in
                   uu____2937.FStar_Syntax_Syntax.n  in
                 match uu____2936 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2942) ->
                     let uu____2967 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2967 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2977 = FStar_Options.print_implicits ()
                               in
                            if uu____2977 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2990 =
                            let uu____2999 =
                              let uu____3000 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3000.FStar_Syntax_Syntax.n  in
                            match uu____2999 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3018 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____3048 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3092  ->
                                                     match uu____3092 with
                                                     | (e2,uu____3100) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____3048, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3112 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____3112)
                                  | uu____3119 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3018 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____3150 ->
                                let uu____3151 = resugar_term' env body2  in
                                ([], uu____3151)
                             in
                          (match uu____2990 with
                           | (pats,body3) ->
                               let uu____3168 = uncurry xs3 pats body3  in
                               (match uu____3168 with
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
                 | uu____3216 ->
                     if op = "forall"
                     then
                       let uu____3217 =
                         let uu____3218 =
                           let uu____3231 = resugar_term' env body  in
                           ([], [[]], uu____3231)  in
                         FStar_Parser_AST.QForall uu____3218  in
                       mk1 uu____3217
                     else
                       (let uu____3243 =
                          let uu____3244 =
                            let uu____3257 = resugar_term' env body  in
                            ([], [[]], uu____3257)  in
                          FStar_Parser_AST.QExists uu____3244  in
                        mk1 uu____3243)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3284)::[] -> resugar b
                  | uu____3301 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3311) ->
               let uu____3316 = FStar_List.hd args1  in
               (match uu____3316 with
                | (e1,uu____3330) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3399  ->
                         match uu____3399 with
                         | (e1,qual) ->
                             let uu____3416 = resugar_term' env e1  in
                             let uu____3417 = resugar_imp env qual  in
                             (uu____3416, uu____3417)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3430 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3430 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3478 =
                               let uu____3479 =
                                 let uu____3486 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3486)  in
                               FStar_Parser_AST.Op uu____3479  in
                             mk1 uu____3478  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3504  ->
                                  match uu____3504 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3519 =
                      let uu____3520 =
                        let uu____3527 =
                          let uu____3530 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3530
                           in
                        (op1, uu____3527)  in
                      FStar_Parser_AST.Op uu____3520  in
                    mk1 uu____3519
                | uu____3543 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3612 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3612 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3658 =
                   let uu____3671 =
                     let uu____3676 = resugar_pat' env pat1 branch_bv  in
                     let uu____3677 = resugar_term' env e  in
                     (uu____3676, uu____3677)  in
                   (FStar_Pervasives_Native.None, uu____3671)  in
                 [uu____3658]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3729,t1)::(pat2,uu____3732,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3828 =
            let uu____3829 =
              let uu____3836 = resugar_term' env e  in
              let uu____3837 = resugar_term' env t1  in
              let uu____3838 = resugar_term' env t2  in
              (uu____3836, uu____3837, uu____3838)  in
            FStar_Parser_AST.If uu____3829  in
          mk1 uu____3828
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3904 =
            match uu____3904 with
            | (pat,wopt,b) ->
                let uu____3946 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3946 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3998 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3998
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4002 =
            let uu____4003 =
              let uu____4018 = resugar_term' env e  in
              let uu____4019 = FStar_List.map resugar_branch branches  in
              (uu____4018, uu____4019)  in
            FStar_Parser_AST.Match uu____4003  in
          mk1 uu____4002
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____4065) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____4134 =
            let uu____4135 =
              let uu____4144 = resugar_term' env e  in
              (uu____4144, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____4135  in
          mk1 uu____4134
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____4170 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____4170 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4223 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____4223
                    in
                 let uu____4230 =
                   let uu____4235 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4235
                    in
                 match uu____4230 with
                 | (univs1,td) ->
                     let uu____4254 =
                       let uu____4261 =
                         let uu____4262 = FStar_Syntax_Subst.compress td  in
                         uu____4262.FStar_Syntax_Syntax.n  in
                       match uu____4261 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4271,(t1,uu____4273)::(d,uu____4275)::[])
                           -> (t1, d)
                       | uu____4332 -> failwith "wrong let binding format"
                        in
                     (match uu____4254 with
                      | (typ,def) ->
                          let uu____4361 =
                            let uu____4376 =
                              let uu____4377 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4377.FStar_Syntax_Syntax.n  in
                            match uu____4376 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4396) ->
                                let uu____4421 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4421 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4451 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4451
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4469 -> ([], def, false)  in
                          (match uu____4361 with
                           | (binders,term,is_pat_app) ->
                               let uu____4519 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4530 =
                                       let uu____4531 =
                                         let uu____4532 =
                                           let uu____4539 =
                                             bv_as_unique_ident bv  in
                                           (uu____4539,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4532
                                          in
                                       mk_pat uu____4531  in
                                     (uu____4530, term)
                                  in
                               (match uu____4519 with
                                | (pat,term1) ->
                                    let uu____4560 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4600  ->
                                                  match uu____4600 with
                                                  | (bv,q) ->
                                                      let uu____4615 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4615
                                                        (fun q1  ->
                                                           let uu____4627 =
                                                             let uu____4628 =
                                                               let uu____4635
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4635,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4628
                                                              in
                                                           mk_pat uu____4627)))
                                           in
                                        let uu____4638 =
                                          let uu____4643 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4643)
                                           in
                                        let uu____4646 =
                                          universe_to_string univs1  in
                                        (uu____4638, uu____4646)
                                      else
                                        (let uu____4652 =
                                           let uu____4657 =
                                             resugar_term' env term1  in
                                           (pat, uu____4657)  in
                                         let uu____4658 =
                                           universe_to_string univs1  in
                                         (uu____4652, uu____4658))
                                       in
                                    (attrs_opt, uu____4560))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4758 =
                   match uu____4758 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4814 =
                         let uu____4815 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4815  in
                       if uu____4814
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4890) ->
          let s =
            let uu____4908 =
              let uu____4909 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____4909 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4908  in
          let uu____4910 = mk1 FStar_Parser_AST.Wild  in label s uu____4910
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____4918 =
            let uu____4919 =
              let uu____4924 = resugar_term' env tm  in (uu____4924, qi1)  in
            FStar_Parser_AST.Quote uu____4919  in
          mk1 uu____4918
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___201_4936 =
            match uu___201_4936 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4944,(uu____4945,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____5006 =
                        let uu____5007 =
                          let uu____5016 = resugar_seq t11  in
                          (uu____5016, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____5007  in
                      mk1 uu____5006
                  | uu____5019 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5063  ->
                         match uu____5063 with
                         | (x,uu____5071) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____5076 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____5091 =
                 let uu____5092 =
                   let uu____5101 = resugar_term' env e  in
                   let uu____5102 =
                     let uu____5103 =
                       let uu____5104 =
                         let uu____5115 =
                           let uu____5122 =
                             let uu____5127 = resugar_term' env t1  in
                             (uu____5127, FStar_Parser_AST.Nothing)  in
                           [uu____5122]  in
                         (name1, uu____5115)  in
                       FStar_Parser_AST.Construct uu____5104  in
                     mk1 uu____5103  in
                   (uu____5101, uu____5102, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5092  in
               mk1 uu____5091
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____5145,t1) ->
               let uu____5151 =
                 let uu____5152 =
                   let uu____5161 = resugar_term' env e  in
                   let uu____5162 =
                     let uu____5163 =
                       let uu____5164 =
                         let uu____5175 =
                           let uu____5182 =
                             let uu____5187 = resugar_term' env t1  in
                             (uu____5187, FStar_Parser_AST.Nothing)  in
                           [uu____5182]  in
                         (name1, uu____5175)  in
                       FStar_Parser_AST.Construct uu____5164  in
                     mk1 uu____5163  in
                   (uu____5161, uu____5162, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____5152  in
               mk1 uu____5151)
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
               let uu____5238 = FStar_Options.print_universes ()  in
               if uu____5238
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
               let uu____5299 = FStar_Options.print_universes ()  in
               if uu____5299
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
            let uu____5340 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5340, FStar_Parser_AST.Nothing)  in
          let uu____5341 = FStar_Options.print_effect_args ()  in
          if uu____5341
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____5362 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____5362
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5445 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5445, (FStar_Pervasives_Native.snd post))  in
                    let uu____5456 =
                      let uu____5465 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5465 then [] else [pre]  in
                    let uu____5497 =
                      let uu____5506 =
                        let uu____5515 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5515 then [] else [pats]  in
                      FStar_List.append [post1] uu____5506  in
                    FStar_List.append uu____5456 uu____5497
                | uu____5571 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5604  ->
                   match uu____5604 with
                   | (e,uu____5616) ->
                       let uu____5621 = resugar_term' env e  in
                       (uu____5621, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___202_5646 =
              match uu___202_5646 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5679 = resugar_term' env e  in
                         (uu____5679, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5684 -> aux l tl1)
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
        let uu____5730 = b  in
        match uu____5730 with
        | (x,aq) ->
            let uu____5739 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____5739
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5753 =
                       let uu____5754 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5754  in
                     FStar_Parser_AST.mk_binder uu____5753 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5755 ->
                     let uu____5756 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5756
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5758 =
                          let uu____5759 =
                            let uu____5764 = bv_as_unique_ident x  in
                            (uu____5764, e)  in
                          FStar_Parser_AST.Annotated uu____5759  in
                        FStar_Parser_AST.mk_binder uu____5758 r
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
              let uu____5784 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5784  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5787 =
                if used
                then
                  let uu____5788 =
                    let uu____5795 = bv_as_unique_ident v1  in
                    (uu____5795, aqual)  in
                  FStar_Parser_AST.PatVar uu____5788
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____5787  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5801;
                  FStar_Syntax_Syntax.vars = uu____5802;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5812 = FStar_Options.print_bound_var_types ()  in
                if uu____5812
                then
                  let uu____5813 =
                    let uu____5814 =
                      let uu____5825 =
                        let uu____5832 = resugar_term' env typ  in
                        (uu____5832, FStar_Pervasives_Native.None)  in
                      (pat, uu____5825)  in
                    FStar_Parser_AST.PatAscribed uu____5814  in
                  mk1 uu____5813
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
          let uu____5852 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____5852
            (fun aqual  ->
               let uu____5864 =
                 let uu____5869 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                   uu____5869
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5864)

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
          (let uu____5932 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5932) &&
            (let uu____5934 =
               FStar_List.existsML
                 (fun uu____5945  ->
                    match uu____5945 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5961)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5966 -> false
                          | uu____5967 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5934)
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
            let uu____6030 = may_drop_implicits args  in
            if uu____6030 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____6050  ->
                 match uu____6050 with
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
              ((let uu____6096 =
                  let uu____6097 =
                    let uu____6098 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____6098  in
                  Prims.op_Negation uu____6097  in
                if uu____6096
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
              let uu____6134 = filter_pattern_imp args  in
              (match uu____6134 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____6174 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____6174 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____6190 =
                       let uu____6195 =
                         let uu____6196 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____6196
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____6195)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____6190);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____6239  ->
                        match uu____6239 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____6251 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____6251)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____6255;
                 FStar_Syntax_Syntax.fv_delta = uu____6256;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____6283 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____6283 FStar_List.rev  in
              let args1 =
                let uu____6299 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____6317  ->
                          match uu____6317 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____6299 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6391 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____6391
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6414 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6414
                 in
              let args2 =
                let uu____6432 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6432 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6474 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6474 with
               | FStar_Pervasives_Native.Some (op,uu____6484) ->
                   let uu____6495 =
                     let uu____6496 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____6496  in
                   mk1 uu____6495
               | FStar_Pervasives_Native.None  ->
                   let uu____6503 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6503 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6508 ->
              let uu____6509 =
                let uu____6510 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____6510  in
              mk1 uu____6509
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
          let uu____6546 =
            let uu____6549 =
              let uu____6550 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____6550  in
            FStar_Pervasives_Native.Some uu____6549  in
          FStar_Pervasives_Native.Some uu____6546

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
          let uu____6560 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____6560

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___203_6567  ->
    match uu___203_6567 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6574 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6575 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6576 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6581 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6590 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6599 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___204_6604  ->
    match uu___204_6604 with
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
            (tylid,uvs,bs,t,uu____6643,datacons) ->
            let uu____6653 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6680,uu____6681,uu____6682,inductive_lid,uu____6684,uu____6685)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6690 -> failwith "unexpected"))
               in
            (match uu____6653 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6709 = FStar_Options.print_implicits ()  in
                   if uu____6709 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6723 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___205_6728  ->
                             match uu___205_6728 with
                             | FStar_Syntax_Syntax.RecordType uu____6729 ->
                                 true
                             | uu____6738 -> false))
                      in
                   if uu____6723
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6790,univs1,term,uu____6793,num,uu____6795)
                           ->
                           let uu____6800 =
                             let uu____6801 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6801.FStar_Syntax_Syntax.n  in
                           (match uu____6800 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6815)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6884  ->
                                          match uu____6884 with
                                          | (b,qual) ->
                                              let uu____6905 =
                                                bv_as_unique_ident b  in
                                              let uu____6906 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6905, uu____6906,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6917 -> failwith "unexpected")
                       | uu____6928 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____7053,num,uu____7055) ->
                            let c =
                              let uu____7073 =
                                let uu____7076 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____7076  in
                              ((l.FStar_Ident.ident), uu____7073,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____7093 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____7167 ->
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
        let uu____7191 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____7191;
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
        let uu____7217 = ts  in
        match uu____7217 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____7229 =
              let uu____7230 =
                let uu____7245 =
                  let uu____7254 =
                    let uu____7261 =
                      let uu____7262 =
                        let uu____7275 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____7275)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____7262  in
                    (uu____7261, FStar_Pervasives_Native.None)  in
                  [uu____7254]  in
                (false, false, uu____7245)  in
              FStar_Parser_AST.Tycon uu____7230  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____7229
  
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
              let uu____7353 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____7353 with
              | (bs,action_defn) ->
                  let uu____7360 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____7360 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____7370 = FStar_Options.print_implicits ()
                            in
                         if uu____7370
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____7377 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____7377 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____7393 =
                             let uu____7404 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____7404,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____7393  in
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
            let uu____7478 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7478 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7488 = FStar_Options.print_implicits ()  in
                  if uu____7488 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7495 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7495 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7563) ->
          let uu____7572 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7594 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7611 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7618 -> false
                    | uu____7633 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7572 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7669 se1 =
                 match uu____7669 with
                 | (datacon_ses1,tycons) ->
                     let uu____7695 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7695 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7710 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7710 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7745 =
                           let uu____7746 =
                             let uu____7747 =
                               let uu____7762 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____7762)  in
                             FStar_Parser_AST.Tycon uu____7747  in
                           decl'_to_decl se uu____7746  in
                         FStar_Pervasives_Native.Some uu____7745
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7793,uu____7794,uu____7795,uu____7796,uu____7797)
                              ->
                              let uu____7802 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7802
                          | uu____7805 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7808 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7814) ->
          let uu____7819 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___206_7825  ->
                    match uu___206_7825 with
                    | FStar_Syntax_Syntax.Projector (uu____7826,uu____7827)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7828 -> true
                    | uu____7829 -> false))
             in
          if uu____7819
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7860) ->
                 let uu____7889 =
                   let uu____7890 =
                     let uu____7891 =
                       let uu____7902 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7902)  in
                     FStar_Parser_AST.TopLevelLet uu____7891  in
                   decl'_to_decl se uu____7890  in
                 FStar_Pervasives_Native.Some uu____7889
             | uu____7939 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7943,fml) ->
          let uu____7945 =
            let uu____7946 =
              let uu____7947 =
                let uu____7952 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7952)  in
              FStar_Parser_AST.Assume uu____7947  in
            decl'_to_decl se uu____7946  in
          FStar_Pervasives_Native.Some uu____7945
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7954 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7954
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7956 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7956
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7965,t) ->
                let uu____7975 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7975
            | uu____7976 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7984,t) ->
                let uu____7994 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7994
            | uu____7995 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____8019 -> failwith "Should not happen hopefully"  in
          let uu____8028 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____8028
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____8038 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____8038 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____8050 = FStar_Options.print_implicits ()  in
                 if uu____8050 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____8063 =
                 let uu____8064 =
                   let uu____8065 =
                     let uu____8080 =
                       let uu____8089 =
                         let uu____8096 =
                           let uu____8097 =
                             let uu____8110 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____8110)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____8097  in
                         (uu____8096, FStar_Pervasives_Native.None)  in
                       [uu____8089]  in
                     (false, false, uu____8080)  in
                   FStar_Parser_AST.Tycon uu____8065  in
                 decl'_to_decl se uu____8064  in
               FStar_Pervasives_Native.Some uu____8063)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____8138 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____8138
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____8142 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___207_8148  ->
                    match uu___207_8148 with
                    | FStar_Syntax_Syntax.Projector (uu____8149,uu____8150)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____8151 -> true
                    | uu____8152 -> false))
             in
          if uu____8142
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____8157 =
                 (let uu____8160 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____8160) || (FStar_List.isEmpty uvs)
                  in
               if uu____8157
               then resugar_term' env t
               else
                 (let uu____8162 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____8162 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____8170 = resugar_term' env t1  in
                      label universes uu____8170)
                in
             let uu____8171 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____8171)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____8178 =
            let uu____8179 =
              let uu____8180 =
                let uu____8187 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____8192 = resugar_term' env t  in
                (uu____8187, uu____8192)  in
              FStar_Parser_AST.Splice uu____8180  in
            decl'_to_decl se uu____8179  in
          FStar_Pervasives_Native.Some uu____8178
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8195 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____8212 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____8227 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____8248 = noenv resugar_term'  in uu____8248 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____8265 = noenv resugar_sigelt'  in uu____8265 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____8282 = noenv resugar_comp'  in uu____8282 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____8304 = noenv resugar_pat'  in uu____8304 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____8337 = noenv resugar_binder'  in uu____8337 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____8361 = noenv resugar_tscheme'  in uu____8361 ts 
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
          let uu____8393 = noenv resugar_eff_decl'  in
          uu____8393 for_free r q ed
  