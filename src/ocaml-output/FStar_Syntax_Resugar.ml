open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____7 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____7
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____11 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____11
  
let map_opt :
  'Auu____16 'Auu____17 .
    Prims.unit ->
      ('Auu____16 -> 'Auu____17 FStar_Pervasives_Native.option) ->
        'Auu____16 Prims.list -> 'Auu____17 Prims.list
  = fun uu____31  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____36 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____36
      then
        let uu____37 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____37
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____41 .
    ('Auu____41,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____41,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___67_95  ->
            match uu___67_95 with
            | (uu____102,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____103)) -> false
            | uu____106 -> true))
  
let filter_pattern_imp :
  'Auu____115 .
    ('Auu____115,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____115,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____145  ->
         match uu____145 with
         | (uu____150,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____214 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____222 = FStar_Options.print_universes ()  in
    if uu____222
    then
      let uu____223 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____223 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____263 ->
          let uu____264 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____264 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____271 =
                      let uu____272 =
                        let uu____273 =
                          let uu____284 = FStar_Util.string_of_int n1  in
                          (uu____284, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____273  in
                      FStar_Parser_AST.Const uu____272  in
                    mk1 uu____271 r
                | uu____295 ->
                    let e1 =
                      let uu____297 =
                        let uu____298 =
                          let uu____299 =
                            let uu____310 = FStar_Util.string_of_int n1  in
                            (uu____310, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____299  in
                        FStar_Parser_AST.Const uu____298  in
                      mk1 uu____297 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____322 =
                      let uu____323 =
                        let uu____330 = FStar_Ident.id_of_text "+"  in
                        (uu____330, [e1; e2])  in
                      FStar_Parser_AST.Op uu____323  in
                    mk1 uu____322 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____336 ->
               let t =
                 let uu____340 =
                   let uu____341 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____341  in
                 mk1 uu____340 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____347 =
                        let uu____348 =
                          let uu____355 = resugar_universe x r  in
                          (acc, uu____355, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____348  in
                      mk1 uu____347 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____357 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____368 =
              let uu____373 =
                let uu____374 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____374  in
              (uu____373, r)  in
            FStar_Ident.mk_ident uu____368  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string,Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___68_397 =
      match uu___68_397 with
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
      | uu____574 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____621 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____633 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____633 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____643 ->
               let op =
                 let uu____647 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____689) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____647
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
      let uu____893 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____893 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____947 ->
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
                (let uu____1018 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1018
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1042 =
      let uu____1043 = FStar_Syntax_Subst.compress t  in
      uu____1043.FStar_Syntax_Syntax.n  in
    match uu____1042 with
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
        let uu____1066 = string_to_op s  in
        (match uu____1066 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1100 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1115 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1123 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1127 -> true
    | uu____1128 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1135 ->
        let uu____1136 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1136
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1144 = may_shorten lid  in
      if uu____1144 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____1213 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1213  in
      let uu____1214 =
        let uu____1215 = FStar_Syntax_Subst.compress t  in
        uu____1215.FStar_Syntax_Syntax.n  in
      match uu____1214 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1218 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1244 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1244
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1247 =
              let uu____1250 = bv_as_unique_ident x  in [uu____1250]  in
            FStar_Ident.lid_of_ids uu____1247  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1253 =
              let uu____1256 = bv_as_unique_ident x  in [uu____1256]  in
            FStar_Ident.lid_of_ids uu____1253  in
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
            let uu____1274 =
              let uu____1275 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1275  in
            mk1 uu____1274
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
               | uu____1285 -> failwith "wrong projector format")
            else
              (let uu____1289 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1292 =
                      let uu____1294 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1294  in
                    let uu____1296 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1292 <> uu____1296)
                  in
               if uu____1289
               then
                 let uu____1299 =
                   let uu____1300 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1300  in
                 mk1 uu____1299
               else
                 (let uu____1302 =
                    let uu____1303 =
                      let uu____1314 = maybe_shorten_fv env fv  in
                      (uu____1314, [])  in
                    FStar_Parser_AST.Construct uu____1303  in
                  mk1 uu____1302))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1332 = FStar_Options.print_universes ()  in
          if uu____1332
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
                   let uu____1361 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1361  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1384 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1391 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1391
          then
            let uu____1392 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1392
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1395 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1404 -> ("Type", true)  in
          (match uu____1395 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1408 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1408  in
               let uu____1409 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1409
               then
                 let uu____1410 =
                   let uu____1411 =
                     let uu____1418 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1418, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1411  in
                 mk1 uu____1410
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1422) ->
          let uu____1443 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1443 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1451 = FStar_Options.print_implicits ()  in
                 if uu____1451 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1468  ->
                         match uu____1468 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____1498 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1498 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1506 = FStar_Options.print_implicits ()  in
                 if uu____1506 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1512 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1512 FStar_List.rev  in
               let rec aux body3 uu___69_1531 =
                 match uu___69_1531 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1547 =
            let uu____1552 =
              let uu____1553 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1553]  in
            FStar_Syntax_Subst.open_term uu____1552 phi  in
          (match uu____1547 with
           | (x1,phi1) ->
               let b =
                 let uu____1557 =
                   let uu____1560 = FStar_List.hd x1  in
                   resugar_binder' env uu____1560 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1557  in
               let uu____1565 =
                 let uu____1566 =
                   let uu____1571 = resugar_term' env phi1  in
                   (b, uu____1571)  in
                 FStar_Parser_AST.Refine uu____1566  in
               mk1 uu____1565)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1573;
             FStar_Syntax_Syntax.vars = uu____1574;_},(e,uu____1576)::[])
          when
          (let uu____1607 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1607) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___70_1649 =
            match uu___70_1649 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1719 -> failwith "last of an empty list"  in
          let rec last_two uu___71_1755 =
            match uu___71_1755 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1786::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____1863::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____1930  ->
                   match uu____1930 with
                   | (e2,qual) ->
                       let uu____1947 = resugar_term' env e2  in
                       let uu____1948 = resugar_imp qual  in
                       (uu____1947, uu____1948)) args1
               in
            let uu____1949 = resugar_term' env e1  in
            match uu____1949 with
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
                     fun uu____1986  ->
                       match uu____1986 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2002 = FStar_Options.print_implicits ()  in
            if uu____2002 then args else filter_imp args  in
          let uu____2014 = resugar_term_as_op e  in
          (match uu____2014 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2025) ->
               (match args1 with
                | (fst1,uu____2031)::(snd1,uu____2033)::rest ->
                    let e1 =
                      let uu____2064 =
                        let uu____2065 =
                          let uu____2072 = FStar_Ident.id_of_text "*"  in
                          let uu____2073 =
                            let uu____2076 = resugar_term' env fst1  in
                            let uu____2077 =
                              let uu____2080 = resugar_term' env snd1  in
                              [uu____2080]  in
                            uu____2076 :: uu____2077  in
                          (uu____2072, uu____2073)  in
                        FStar_Parser_AST.Op uu____2065  in
                      mk1 uu____2064  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2093  ->
                           match uu____2093 with
                           | (x,uu____2099) ->
                               let uu____2100 =
                                 let uu____2101 =
                                   let uu____2108 =
                                     FStar_Ident.id_of_text "*"  in
                                   let uu____2109 =
                                     let uu____2112 =
                                       let uu____2115 = resugar_term' env x
                                          in
                                       [uu____2115]  in
                                     e1 :: uu____2112  in
                                   (uu____2108, uu____2109)  in
                                 FStar_Parser_AST.Op uu____2101  in
                               mk1 uu____2100) e1 rest
                | uu____2118 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2127) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2153)::[] -> b
                 | uu____2170 -> failwith "wrong arguments to dtuple"  in
               let uu____2181 =
                 let uu____2182 = FStar_Syntax_Subst.compress body  in
                 uu____2182.FStar_Syntax_Syntax.n  in
               (match uu____2181 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2187) ->
                    let uu____2208 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2208 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2216 = FStar_Options.print_implicits ()
                              in
                           if uu____2216 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2228 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2249  ->
                              match uu____2249 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2261) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2267) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2272 = FStar_List.hd args1  in
               (match uu____2272 with
                | (t1,uu____2286) ->
                    let uu____2291 =
                      let uu____2292 = FStar_Syntax_Subst.compress t1  in
                      uu____2292.FStar_Syntax_Syntax.n  in
                    (match uu____2291 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2297 =
                           let uu____2298 =
                             let uu____2303 = resugar_term' env t1  in
                             (uu____2303, f)  in
                           FStar_Parser_AST.Project uu____2298  in
                         mk1 uu____2297
                     | uu____2304 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2305) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2325 =
                 match new_args with
                 | (a1,uu____2343)::(a2,uu____2345)::[] -> (a1, a2)
                 | uu____2376 -> failwith "wrong arguments to try_with"  in
               (match uu____2325 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2407 =
                        let uu____2408 = FStar_Syntax_Subst.compress term  in
                        uu____2408.FStar_Syntax_Syntax.n  in
                      match uu____2407 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2413) ->
                          let uu____2434 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2434 with | (x1,e2) -> e2)
                      | uu____2441 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2443 = decomp body  in
                      resugar_term' env uu____2443  in
                    let handler1 =
                      let uu____2445 = decomp handler  in
                      resugar_term' env uu____2445  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2451,uu____2452,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2484,uu____2485,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2522 =
                            let uu____2523 =
                              let uu____2532 = resugar_body t11  in
                              (uu____2532, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2523  in
                          mk1 uu____2522
                      | uu____2535 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2590 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2620) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2626) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2711 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2722 =
                   let uu____2723 = FStar_Syntax_Subst.compress body  in
                   uu____2723.FStar_Syntax_Syntax.n  in
                 match uu____2722 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2728) ->
                     let uu____2749 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2749 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2757 = FStar_Options.print_implicits ()
                               in
                            if uu____2757 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2766 =
                            let uu____2775 =
                              let uu____2776 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2776.FStar_Syntax_Syntax.n  in
                            match uu____2775 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____2794 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____2822 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____2858  ->
                                                     match uu____2858 with
                                                     | (e2,uu____2864) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____2822, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____2872 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____2872)
                                  | uu____2879 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____2794 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____2910 ->
                                let uu____2911 = resugar_term' env body2  in
                                ([], uu____2911)
                             in
                          (match uu____2766 with
                           | (pats,body3) ->
                               let uu____2928 = uncurry xs3 pats body3  in
                               (match uu____2928 with
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
                 | uu____2976 ->
                     if op = "forall"
                     then
                       let uu____2977 =
                         let uu____2978 =
                           let uu____2991 = resugar_term' env body  in
                           ([], [[]], uu____2991)  in
                         FStar_Parser_AST.QForall uu____2978  in
                       mk1 uu____2977
                     else
                       (let uu____3003 =
                          let uu____3004 =
                            let uu____3017 = resugar_term' env body  in
                            ([], [[]], uu____3017)  in
                          FStar_Parser_AST.QExists uu____3004  in
                        mk1 uu____3003)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3044)::[] -> resugar b
                  | uu____3061 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3071) ->
               let uu____3076 = FStar_List.hd args1  in
               (match uu____3076 with
                | (e1,uu____3090) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3157  ->
                         match uu____3157 with
                         | (e1,qual) ->
                             let uu____3174 = resugar_term' env e1  in
                             let uu____3175 = resugar_imp qual  in
                             (uu____3174, uu____3175)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3188 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3188 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3236 =
                               let uu____3237 =
                                 let uu____3244 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3244)  in
                               FStar_Parser_AST.Op uu____3237  in
                             mk1 uu____3236  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3262  ->
                                  match uu____3262 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3277 =
                      let uu____3278 =
                        let uu____3285 =
                          let uu____3288 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3288
                           in
                        (op1, uu____3285)  in
                      FStar_Parser_AST.Op uu____3278  in
                    mk1 uu____3277
                | uu____3301 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3370 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3370 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3416 =
                   let uu____3429 =
                     let uu____3434 = resugar_pat' env pat1 branch_bv  in
                     let uu____3435 = resugar_term' env e  in
                     (uu____3434, uu____3435)  in
                   (FStar_Pervasives_Native.None, uu____3429)  in
                 [uu____3416]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3487,t1)::(pat2,uu____3490,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3586 =
            let uu____3587 =
              let uu____3594 = resugar_term' env e  in
              let uu____3595 = resugar_term' env t1  in
              let uu____3596 = resugar_term' env t2  in
              (uu____3594, uu____3595, uu____3596)  in
            FStar_Parser_AST.If uu____3587  in
          mk1 uu____3586
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3660 =
            match uu____3660 with
            | (pat,wopt,b) ->
                let uu____3702 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3702 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3754 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3754
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3758 =
            let uu____3759 =
              let uu____3774 = resugar_term' env e  in
              let uu____3775 = FStar_List.map resugar_branch branches  in
              (uu____3774, uu____3775)  in
            FStar_Parser_AST.Match uu____3759  in
          mk1 uu____3758
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3821) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____3888 =
            let uu____3889 =
              let uu____3898 = resugar_term' env e  in
              (uu____3898, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____3889  in
          mk1 uu____3888
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____3922 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____3922 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____3973 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____3973
                    in
                 let uu____3978 =
                   let uu____3983 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____3983
                    in
                 match uu____3978 with
                 | (univs1,td) ->
                     let uu____4002 =
                       let uu____4011 =
                         let uu____4012 = FStar_Syntax_Subst.compress td  in
                         uu____4012.FStar_Syntax_Syntax.n  in
                       match uu____4011 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4023,(t1,uu____4025)::(d,uu____4027)::[])
                           -> (t1, d)
                       | uu____4070 -> failwith "wrong let binding format"
                        in
                     (match uu____4002 with
                      | (typ,def) ->
                          let uu____4105 =
                            let uu____4112 =
                              let uu____4113 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4113.FStar_Syntax_Syntax.n  in
                            match uu____4112 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4124) ->
                                let uu____4145 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4145 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4159 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4159
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4161 -> ([], def, false)  in
                          (match uu____4105 with
                           | (binders,term,is_pat_app) ->
                               let uu____4193 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4204 =
                                       let uu____4205 =
                                         let uu____4206 =
                                           let uu____4213 =
                                             bv_as_unique_ident bv  in
                                           (uu____4213,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4206
                                          in
                                       mk_pat uu____4205  in
                                     (uu____4204, term)
                                  in
                               (match uu____4193 with
                                | (pat,term1) ->
                                    let uu____4234 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4266  ->
                                                  match uu____4266 with
                                                  | (bv,q) ->
                                                      let uu____4281 =
                                                        resugar_arg_qual q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4281
                                                        (fun q1  ->
                                                           let uu____4293 =
                                                             let uu____4294 =
                                                               let uu____4301
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4301,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4294
                                                              in
                                                           mk_pat uu____4293)))
                                           in
                                        let uu____4304 =
                                          let uu____4309 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4309)
                                           in
                                        let uu____4312 =
                                          universe_to_string univs1  in
                                        (uu____4304, uu____4312)
                                      else
                                        (let uu____4318 =
                                           let uu____4323 =
                                             resugar_term' env term1  in
                                           (pat, uu____4323)  in
                                         let uu____4324 =
                                           universe_to_string univs1  in
                                         (uu____4318, uu____4324))
                                       in
                                    (attrs_opt, uu____4234))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4422 =
                   match uu____4422 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4478 =
                         let uu____4479 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4479  in
                       if uu____4478
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4554) ->
          let s =
            let uu____4580 =
              let uu____4581 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_All.pipe_right uu____4581 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4580  in
          let uu____4582 = mk1 FStar_Parser_AST.Wild  in label s uu____4582
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____4590 =
            let uu____4591 =
              let uu____4596 = resugar_term' env tm  in (uu____4596, qi1)  in
            FStar_Parser_AST.Quote uu____4591  in
          mk1 uu____4590
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___72_4606 =
            match uu___72_4606 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4612,(uu____4613,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____4674 =
                        let uu____4675 =
                          let uu____4684 = resugar_seq t11  in
                          (uu____4684, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____4675  in
                      mk1 uu____4674
                  | uu____4687 -> t1  in
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
                 | uu____4733 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval  ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                let uu____4735 =
                  let uu____4736 = FStar_Syntax_Subst.compress e  in
                  uu____4736.FStar_Syntax_Syntax.n  in
                (match uu____4735 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____4740;
                        FStar_Syntax_Syntax.vars = uu____4741;_},(term,uu____4743)::[])
                     -> resugar_term' env term
                 | uu____4772 -> failwith "mutable_rval should have app term")
             in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____4810  ->
                         match uu____4810 with
                         | (x,uu____4816) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l,uu____4818,p) ->
               let uu____4820 =
                 let uu____4821 =
                   let uu____4828 = resugar_term' env e  in
                   (uu____4828, l, p)  in
                 FStar_Parser_AST.Labeled uu____4821  in
               mk1 uu____4820
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____4837 =
                 let uu____4838 =
                   let uu____4847 = resugar_term' env e  in
                   let uu____4848 =
                     let uu____4849 =
                       let uu____4850 =
                         let uu____4861 =
                           let uu____4868 =
                             let uu____4873 = resugar_term' env t1  in
                             (uu____4873, FStar_Parser_AST.Nothing)  in
                           [uu____4868]  in
                         (name1, uu____4861)  in
                       FStar_Parser_AST.Construct uu____4850  in
                     mk1 uu____4849  in
                   (uu____4847, uu____4848, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____4838  in
               mk1 uu____4837
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4891,t1) ->
               let uu____4897 =
                 let uu____4898 =
                   let uu____4907 = resugar_term' env e  in
                   let uu____4908 =
                     let uu____4909 =
                       let uu____4910 =
                         let uu____4921 =
                           let uu____4928 =
                             let uu____4933 = resugar_term' env t1  in
                             (uu____4933, FStar_Parser_AST.Nothing)  in
                           [uu____4928]  in
                         (name1, uu____4921)  in
                       FStar_Parser_AST.Construct uu____4910  in
                     mk1 uu____4909  in
                   (uu____4907, uu____4908, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____4898  in
               mk1 uu____4897)
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
               let uu____4982 = FStar_Options.print_universes ()  in
               if uu____4982
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
               let uu____5043 = FStar_Options.print_universes ()  in
               if uu____5043
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
            let uu____5084 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5084, FStar_Parser_AST.Nothing)  in
          let uu____5085 = FStar_Options.print_effect_args ()  in
          if uu____5085
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____5104 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____5104
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5173 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5173, (FStar_Pervasives_Native.snd post))  in
                    let uu____5182 =
                      let uu____5191 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5191 then [] else [pre]  in
                    let uu____5221 =
                      let uu____5230 =
                        let uu____5239 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5239 then [] else [pats]  in
                      FStar_List.append [post1] uu____5230  in
                    FStar_List.append uu____5182 uu____5221
                | uu____5293 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5322  ->
                   match uu____5322 with
                   | (e,uu____5332) ->
                       let uu____5333 = resugar_term' env e  in
                       (uu____5333, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___73_5354 =
              match uu___73_5354 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5387 = resugar_term' env e  in
                         (uu____5387, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5392 -> aux l tl1)
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
        let uu____5438 = b  in
        match uu____5438 with
        | (x,aq) ->
            let uu____5443 = resugar_arg_qual aq  in
            FStar_Util.map_opt uu____5443
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5457 =
                       let uu____5458 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5458  in
                     FStar_Parser_AST.mk_binder uu____5457 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5459 ->
                     let uu____5460 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5460
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5462 =
                          let uu____5463 =
                            let uu____5468 = bv_as_unique_ident x  in
                            (uu____5468, e)  in
                          FStar_Parser_AST.Annotated uu____5463  in
                        FStar_Parser_AST.mk_binder uu____5462 r
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
              let uu____5486 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5486  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5489 =
                if used
                then
                  let uu____5490 =
                    let uu____5497 = bv_as_unique_ident v1  in
                    (uu____5497, aqual)  in
                  FStar_Parser_AST.PatVar uu____5490
                else FStar_Parser_AST.PatWild  in
              mk1 uu____5489  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5503;
                  FStar_Syntax_Syntax.vars = uu____5504;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5514 = FStar_Options.print_bound_var_types ()  in
                if uu____5514
                then
                  let uu____5515 =
                    let uu____5516 =
                      let uu____5527 =
                        let uu____5534 = resugar_term' env typ  in
                        (uu____5534, FStar_Pervasives_Native.None)  in
                      (pat, uu____5527)  in
                    FStar_Parser_AST.PatAscribed uu____5516  in
                  mk1 uu____5515
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
          let uu____5552 = resugar_arg_qual qual  in
          FStar_Util.map_opt uu____5552
            (fun aqual  ->
               let uu____5564 =
                 let uu____5569 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                   uu____5569
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5564)

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
          (let uu____5618 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5618) &&
            (let uu____5620 =
               FStar_List.existsML
                 (fun uu____5631  ->
                    match uu____5631 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5647)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5652 -> false
                          | uu____5653 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5620)
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
            let uu____5706 = may_drop_implicits args  in
            if uu____5706 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____5728  ->
                 match uu____5728 with
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
              ((let uu____5774 =
                  let uu____5775 =
                    let uu____5776 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____5776  in
                  Prims.op_Negation uu____5775  in
                if uu____5774
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
              let uu____5812 = filter_pattern_imp args  in
              (match uu____5812 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____5852 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____5852 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____5868 =
                       let uu____5873 =
                         let uu____5874 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____5874
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____5873)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____5868);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____5919  ->
                        match uu____5919 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____5931 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____5931)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____5935;
                 FStar_Syntax_Syntax.fv_delta = uu____5936;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____5963 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____5963 FStar_List.rev  in
              let args1 =
                let uu____5979 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____5999  ->
                          match uu____5999 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____5979 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6069 = map21 tl1 []  in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6069
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6092 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6092
                 in
              let args2 =
                let uu____6110 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6110 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6152 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6152 with
               | FStar_Pervasives_Native.Some (op,uu____6162) ->
                   let uu____6173 =
                     let uu____6174 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____6174  in
                   mk1 uu____6173
               | FStar_Pervasives_Native.None  ->
                   let uu____6181 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6181 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6186 ->
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
  fun uu___74_6199  ->
    match uu___74_6199 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6208 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6209 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6210 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6215 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6224 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6233 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___75_6236  ->
    match uu___75_6236 with
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
            (tylid,uvs,bs,t,uu____6266,datacons) ->
            let uu____6276 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6303,uu____6304,uu____6305,inductive_lid,uu____6307,uu____6308)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6313 -> failwith "unexpected"))
               in
            (match uu____6276 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6332 = FStar_Options.print_implicits ()  in
                   if uu____6332 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6342 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___76_6347  ->
                             match uu___76_6347 with
                             | FStar_Syntax_Syntax.RecordType uu____6348 ->
                                 true
                             | uu____6357 -> false))
                      in
                   if uu____6342
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6405,univs1,term,uu____6408,num,uu____6410)
                           ->
                           let uu____6415 =
                             let uu____6416 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6416.FStar_Syntax_Syntax.n  in
                           (match uu____6415 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6430)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6491  ->
                                          match uu____6491 with
                                          | (b,qual) ->
                                              let uu____6506 =
                                                let uu____6507 =
                                                  bv_as_unique_ident b  in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6507
                                                 in
                                              let uu____6508 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6506, uu____6508,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6519 -> failwith "unexpected")
                       | uu____6530 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____6651,num,uu____6653) ->
                            let c =
                              let uu____6671 =
                                let uu____6674 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____6674  in
                              ((l.FStar_Ident.ident), uu____6671,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____6691 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____6767 ->
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
        let uu____6785 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6785;
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
        let uu____6801 = ts  in
        match uu____6801 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____6809 =
              let uu____6810 =
                let uu____6823 =
                  let uu____6832 =
                    let uu____6839 =
                      let uu____6840 =
                        let uu____6853 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____6853)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____6840  in
                    (uu____6839, FStar_Pervasives_Native.None)  in
                  [uu____6832]  in
                (false, uu____6823)  in
              FStar_Parser_AST.Tycon uu____6810  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6809
  
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
              let uu____6913 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____6913 with
              | (bs,action_defn) ->
                  let uu____6920 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____6920 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____6928 = FStar_Options.print_implicits ()
                            in
                         if uu____6928
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____6933 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____6933 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____6947 =
                             let uu____6958 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____6958,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____6947  in
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
            let uu____7032 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7032 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7040 = FStar_Options.print_implicits ()  in
                  if uu____7040 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7045 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7045 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7105) ->
          let uu____7114 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7136 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7153 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7160 -> false
                    | uu____7175 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7114 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7207 se1 =
                 match uu____7207 with
                 | (datacon_ses1,tycons) ->
                     let uu____7233 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7233 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7248 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7248 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7283 =
                           let uu____7284 =
                             let uu____7285 =
                               let uu____7298 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, uu____7298)  in
                             FStar_Parser_AST.Tycon uu____7285  in
                           decl'_to_decl se uu____7284  in
                         FStar_Pervasives_Native.Some uu____7283
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7329,uu____7330,uu____7331,uu____7332,uu____7333)
                              ->
                              let uu____7338 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7338
                          | uu____7341 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7344 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7350) ->
          let uu____7355 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___77_7361  ->
                    match uu___77_7361 with
                    | FStar_Syntax_Syntax.Projector (uu____7362,uu____7363)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7364 -> true
                    | uu____7365 -> false))
             in
          if uu____7355
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7388) ->
                 let uu____7417 =
                   let uu____7418 =
                     let uu____7419 =
                       let uu____7430 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7430)  in
                     FStar_Parser_AST.TopLevelLet uu____7419  in
                   decl'_to_decl se uu____7418  in
                 FStar_Pervasives_Native.Some uu____7417
             | uu____7467 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7471,fml) ->
          let uu____7473 =
            let uu____7474 =
              let uu____7475 =
                let uu____7480 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7480)  in
              FStar_Parser_AST.Assume uu____7475  in
            decl'_to_decl se uu____7474  in
          FStar_Pervasives_Native.Some uu____7473
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7482 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7482
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7484 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7484
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7493,t) ->
                let uu____7505 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7505
            | uu____7506 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7514,t) ->
                let uu____7526 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7526
            | uu____7527 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7551 -> failwith "Should not happen hopefully"  in
          let uu____7560 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____7560
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____7570 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7570 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____7580 = FStar_Options.print_implicits ()  in
                 if uu____7580 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____7589 =
                 let uu____7590 =
                   let uu____7591 =
                     let uu____7604 =
                       let uu____7613 =
                         let uu____7620 =
                           let uu____7621 =
                             let uu____7634 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____7634)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____7621  in
                         (uu____7620, FStar_Pervasives_Native.None)  in
                       [uu____7613]  in
                     (false, uu____7604)  in
                   FStar_Parser_AST.Tycon uu____7591  in
                 decl'_to_decl se uu____7590  in
               FStar_Pervasives_Native.Some uu____7589)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____7662 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____7662
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____7666 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___78_7672  ->
                    match uu___78_7672 with
                    | FStar_Syntax_Syntax.Projector (uu____7673,uu____7674)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7675 -> true
                    | uu____7676 -> false))
             in
          if uu____7666
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____7681 =
                 (let uu____7684 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____7684) || (FStar_List.isEmpty uvs)
                  in
               if uu____7681
               then resugar_term' env t
               else
                 (let uu____7686 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____7686 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____7694 = resugar_term' env t1  in
                      label universes uu____7694)
                in
             let uu____7695 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____7695)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____7702 =
            let uu____7703 =
              let uu____7704 =
                let uu____7711 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____7716 = resugar_term' env t  in
                (uu____7711, uu____7716)  in
              FStar_Parser_AST.Splice uu____7704  in
            decl'_to_decl se uu____7703  in
          FStar_Pervasives_Native.Some uu____7702
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7719 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____7736 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____7751 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) = FStar_Syntax_DsEnv.empty_env () 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____7767 = noenv resugar_term'  in uu____7767 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____7779 = noenv resugar_sigelt'  in uu____7779 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____7791 = noenv resugar_comp'  in uu____7791 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____7806 = noenv resugar_pat'  in uu____7806 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____7829 = noenv resugar_binder'  in uu____7829 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____7845 = noenv resugar_tscheme'  in uu____7845 ts 
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
          let uu____7866 = noenv resugar_eff_decl'  in
          uu____7866 for_free r q ed
  