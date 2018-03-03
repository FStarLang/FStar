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
      ('Auu____17 -> 'Auu____16 FStar_Pervasives_Native.option) ->
        'Auu____17 Prims.list -> 'Auu____16 Prims.list
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
         (fun uu___66_95  ->
            match uu___66_95 with
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
  FStar_ToSyntax_Env.env ->
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
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____327 ->
               let t =
                 let uu____331 =
                   let uu____332 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____332  in
                 mk1 uu____331 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____338 =
                        let uu____339 =
                          let uu____346 = resugar_universe x r  in
                          (acc, uu____346, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____339  in
                      mk1 uu____338 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____348 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____359 =
              let uu____364 =
                let uu____365 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____365  in
              (uu____364, r)  in
            FStar_Ident.mk_ident uu____359  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___67_384 =
      match uu___67_384 with
      | "Amp" -> FStar_Pervasives_Native.Some ("&", (Prims.parse_int "0"))
      | "At" -> FStar_Pervasives_Native.Some ("@", (Prims.parse_int "0"))
      | "Plus" -> FStar_Pervasives_Native.Some ("+", (Prims.parse_int "0"))
      | "Minus" -> FStar_Pervasives_Native.Some ("-", (Prims.parse_int "0"))
      | "Subtraction" ->
          FStar_Pervasives_Native.Some ("-", (Prims.parse_int "2"))
      | "Tilde" -> FStar_Pervasives_Native.Some ("~", (Prims.parse_int "0"))
      | "Slash" -> FStar_Pervasives_Native.Some ("/", (Prims.parse_int "0"))
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", (Prims.parse_int "0"))
      | "Less" -> FStar_Pervasives_Native.Some ("<", (Prims.parse_int "0"))
      | "Equals" -> FStar_Pervasives_Native.Some ("=", (Prims.parse_int "0"))
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", (Prims.parse_int "0"))
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", (Prims.parse_int "0"))
      | "Bar" -> FStar_Pervasives_Native.Some ("|", (Prims.parse_int "0"))
      | "Bang" -> FStar_Pervasives_Native.Some ("!", (Prims.parse_int "0"))
      | "Hat" -> FStar_Pervasives_Native.Some ("^", (Prims.parse_int "0"))
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", (Prims.parse_int "0"))
      | "Star" -> FStar_Pervasives_Native.Some ("*", (Prims.parse_int "0"))
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", (Prims.parse_int "0"))
      | "Colon" -> FStar_Pervasives_Native.Some (":", (Prims.parse_int "0"))
      | "Dollar" -> FStar_Pervasives_Native.Some ("$", (Prims.parse_int "0"))
      | "Dot" -> FStar_Pervasives_Native.Some (".", (Prims.parse_int "0"))
      | uu____475 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____502 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____512 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____512 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____520 ->
               let op =
                 let uu____524 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____558) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____524
                  in
               FStar_Pervasives_Native.Some (op, (Prims.parse_int "0")))
        else FStar_Pervasives_Native.None
  
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
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
      let uu____744 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____744 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____792 ->
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
          then FStar_Pervasives_Native.Some ("dtuple", (Prims.parse_int "0"))
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some ("tuple", (Prims.parse_int "0"))
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", (Prims.parse_int "0"))
              else
                (let uu____845 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____845
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None)
       in
    let uu____861 =
      let uu____862 = FStar_Syntax_Subst.compress t  in
      uu____862.FStar_Syntax_Syntax.n  in
    match uu____861 with
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
        let uu____885 = string_to_op s  in
        (match uu____885 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____911 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____924 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____932 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____936 -> true
    | uu____937 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____944 ->
        let uu____945 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____945
  
let (maybe_shorten_fv :
  FStar_ToSyntax_Env.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____953 = may_shorten lid  in
      if uu____953 then FStar_ToSyntax_Env.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_ToSyntax_Env.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____1022 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1022  in
      let uu____1023 =
        let uu____1024 = FStar_Syntax_Subst.compress t  in
        uu____1024.FStar_Syntax_Syntax.n  in
      match uu____1023 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1027 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1053 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1053
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1056 =
              let uu____1059 = bv_as_unique_ident x  in [uu____1059]  in
            FStar_Ident.lid_of_ids uu____1056  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1062 =
              let uu____1065 = bv_as_unique_ident x  in [uu____1065]  in
            FStar_Ident.lid_of_ids uu____1062  in
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
            let uu____1083 =
              let uu____1084 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1084  in
            mk1 uu____1083
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
               | uu____1094 -> failwith "wrong projector format")
            else
              (let uu____1098 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1101 =
                      let uu____1103 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1103  in
                    let uu____1105 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1101 <> uu____1105)
                  in
               if uu____1098
               then
                 let uu____1108 =
                   let uu____1109 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1109  in
                 mk1 uu____1108
               else
                 (let uu____1111 =
                    let uu____1112 =
                      let uu____1123 = maybe_shorten_fv env fv  in
                      (uu____1123, [])  in
                    FStar_Parser_AST.Construct uu____1112  in
                  mk1 uu____1111))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1141 = FStar_Options.print_universes ()  in
          if uu____1141
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
                   let uu____1170 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1170  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1193 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1200 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1200
          then
            let uu____1201 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1201
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1204 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1213 -> ("Type", true)  in
          (match uu____1204 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1217 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1217  in
               let uu____1218 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1218
               then
                 let uu____1219 =
                   let uu____1220 =
                     let uu____1227 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1227, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1220  in
                 mk1 uu____1219
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1231) ->
          let uu____1252 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1252 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1260 = FStar_Options.print_implicits ()  in
                 if uu____1260 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1277  ->
                         match uu____1277 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____1307 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1307 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1315 = FStar_Options.print_implicits ()  in
                 if uu____1315 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1321 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1321 FStar_List.rev  in
               let rec aux body3 uu___68_1340 =
                 match uu___68_1340 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1356 =
            let uu____1361 =
              let uu____1362 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1362]  in
            FStar_Syntax_Subst.open_term uu____1361 phi  in
          (match uu____1356 with
           | (x1,phi1) ->
               let b =
                 let uu____1366 =
                   let uu____1369 = FStar_List.hd x1  in
                   resugar_binder' env uu____1369 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1366  in
               let uu____1374 =
                 let uu____1375 =
                   let uu____1380 = resugar_term' env phi1  in
                   (b, uu____1380)  in
                 FStar_Parser_AST.Refine uu____1375  in
               mk1 uu____1374)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1382;
             FStar_Syntax_Syntax.vars = uu____1383;_},(e,uu____1385)::[])
          when
          (let uu____1416 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1416) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___69_1458 =
            match uu___69_1458 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1528 -> failwith "last of an empty list"  in
          let rec last_two uu___70_1564 =
            match uu___70_1564 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1595::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____1672::t1 -> last_two t1  in
          let rec last_three uu___71_1713 =
            match uu___71_1713 with
            | [] ->
                failwith
                  "last three elements of a list with less than three elements "
            | uu____1744::[] ->
                failwith
                  "last three elements of a list with less than three elements "
            | uu____1771::uu____1772::[] ->
                failwith
                  "last three elements of a list with less than three elements "
            | a1::a2::a3::[] -> [a1; a2; a3]
            | uu____1880::t1 -> last_three t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____1947  ->
                   match uu____1947 with
                   | (e2,qual) ->
                       let uu____1964 = resugar_term' env e2  in
                       let uu____1965 = resugar_imp qual  in
                       (uu____1964, uu____1965)) args1
               in
            let uu____1966 = resugar_term' env e1  in
            match uu____1966 with
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
                     fun uu____2003  ->
                       match uu____2003 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2019 = FStar_Options.print_implicits ()  in
            if uu____2019 then args else filter_imp args  in
          let uu____2031 = resugar_term_as_op e  in
          (match uu____2031 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2042) ->
               (match args1 with
                | (fst1,uu____2048)::(snd1,uu____2050)::rest ->
                    let e1 =
                      let uu____2081 =
                        let uu____2082 =
                          let uu____2089 =
                            let uu____2092 = resugar_term' env fst1  in
                            let uu____2093 =
                              let uu____2096 = resugar_term' env snd1  in
                              [uu____2096]  in
                            uu____2092 :: uu____2093  in
                          ((FStar_Ident.id_of_text "*"), uu____2089)  in
                        FStar_Parser_AST.Op uu____2082  in
                      mk1 uu____2081  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2109  ->
                           match uu____2109 with
                           | (x,uu____2115) ->
                               let uu____2116 =
                                 let uu____2117 =
                                   let uu____2124 =
                                     let uu____2127 =
                                       let uu____2130 = resugar_term' env x
                                          in
                                       [uu____2130]  in
                                     e1 :: uu____2127  in
                                   ((FStar_Ident.id_of_text "*"), uu____2124)
                                    in
                                 FStar_Parser_AST.Op uu____2117  in
                               mk1 uu____2116) e1 rest
                | uu____2133 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2142) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2168)::[] -> b
                 | uu____2185 -> failwith "wrong arguments to dtuple"  in
               let uu____2196 =
                 let uu____2197 = FStar_Syntax_Subst.compress body  in
                 uu____2197.FStar_Syntax_Syntax.n  in
               (match uu____2196 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2202) ->
                    let uu____2223 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2223 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2231 = FStar_Options.print_implicits ()
                              in
                           if uu____2231 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2243 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2264  ->
                              match uu____2264 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2276) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2282) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2287 = FStar_List.hd args1  in
               (match uu____2287 with
                | (t1,uu____2301) ->
                    let uu____2306 =
                      let uu____2307 = FStar_Syntax_Subst.compress t1  in
                      uu____2307.FStar_Syntax_Syntax.n  in
                    (match uu____2306 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2312 =
                           let uu____2313 =
                             let uu____2318 = resugar_term' env t1  in
                             (uu____2318, f)  in
                           FStar_Parser_AST.Project uu____2313  in
                         mk1 uu____2312
                     | uu____2319 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2320) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2340 =
                 match new_args with
                 | (a1,uu____2358)::(a2,uu____2360)::[] -> (a1, a2)
                 | uu____2391 -> failwith "wrong arguments to try_with"  in
               (match uu____2340 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2422 =
                        let uu____2423 = FStar_Syntax_Subst.compress term  in
                        uu____2423.FStar_Syntax_Syntax.n  in
                      match uu____2422 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2428) ->
                          let uu____2449 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2449 with | (x1,e2) -> e2)
                      | uu____2456 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2458 = decomp body  in
                      resugar_term' env uu____2458  in
                    let handler1 =
                      let uu____2460 = decomp handler  in
                      resugar_term' env uu____2460  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2466,uu____2467,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2499,uu____2500,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2537 =
                            let uu____2538 =
                              let uu____2547 = resugar_body t11  in
                              (uu____2547, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2538  in
                          mk1 uu____2537
                      | uu____2550 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2605 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2635) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2641) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2726 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2737 =
                   let uu____2738 = FStar_Syntax_Subst.compress body  in
                   uu____2738.FStar_Syntax_Syntax.n  in
                 match uu____2737 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2743) ->
                     let uu____2764 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2764 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2772 = FStar_Options.print_implicits ()
                               in
                            if uu____2772 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2781 =
                            let uu____2790 =
                              let uu____2791 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2791.FStar_Syntax_Syntax.n  in
                            match uu____2790 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____2809 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____2837 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____2873  ->
                                                     match uu____2873 with
                                                     | (e2,uu____2879) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____2837, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____2887 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____2887)
                                  | uu____2894 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____2809 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____2925 ->
                                let uu____2926 = resugar_term' env body2  in
                                ([], uu____2926)
                             in
                          (match uu____2781 with
                           | (pats,body3) ->
                               let uu____2943 = uncurry xs3 pats body3  in
                               (match uu____2943 with
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
                 | uu____2991 ->
                     if op = "forall"
                     then
                       let uu____2992 =
                         let uu____2993 =
                           let uu____3006 = resugar_term' env body  in
                           ([], [[]], uu____3006)  in
                         FStar_Parser_AST.QForall uu____2993  in
                       mk1 uu____2992
                     else
                       (let uu____3018 =
                          let uu____3019 =
                            let uu____3032 = resugar_term' env body  in
                            ([], [[]], uu____3032)  in
                          FStar_Parser_AST.QExists uu____3019  in
                        mk1 uu____3018)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3059)::[] -> resugar b
                  | uu____3076 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3086) ->
               let uu____3091 = FStar_List.hd args1  in
               (match uu____3091 with
                | (e1,uu____3105) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3150  ->
                         match uu____3150 with
                         | (e1,qual) -> resugar_term' env e1))
                  in
               (match arity with
                | _0_39 when _0_39 = (Prims.parse_int "0") ->
                    let uu____3157 =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    (match uu____3157 with
                     | _0_40 when
                         (_0_40 = (Prims.parse_int "1")) &&
                           ((FStar_List.length args1) > (Prims.parse_int "0"))
                         ->
                         let uu____3164 =
                           let uu____3165 =
                             let uu____3172 =
                               let uu____3175 = last1 args1  in
                               resugar uu____3175  in
                             (op1, uu____3172)  in
                           FStar_Parser_AST.Op uu____3165  in
                         mk1 uu____3164
                     | _0_41 when
                         (_0_41 = (Prims.parse_int "2")) &&
                           ((FStar_List.length args1) > (Prims.parse_int "1"))
                         ->
                         let uu____3190 =
                           let uu____3191 =
                             let uu____3198 =
                               let uu____3201 = last_two args1  in
                               resugar uu____3201  in
                             (op1, uu____3198)  in
                           FStar_Parser_AST.Op uu____3191  in
                         mk1 uu____3190
                     | _0_42 when
                         (_0_42 = (Prims.parse_int "3")) &&
                           ((FStar_List.length args1) > (Prims.parse_int "2"))
                         ->
                         let uu____3216 =
                           let uu____3217 =
                             let uu____3224 =
                               let uu____3227 = last_three args1  in
                               resugar uu____3227  in
                             (op1, uu____3224)  in
                           FStar_Parser_AST.Op uu____3217  in
                         mk1 uu____3216
                     | uu____3236 -> resugar_as_app e args1)
                | _0_43 when
                    (_0_43 = (Prims.parse_int "2")) &&
                      ((FStar_List.length args1) > (Prims.parse_int "1"))
                    ->
                    let uu____3243 =
                      let uu____3244 =
                        let uu____3251 =
                          let uu____3254 = last_two args1  in
                          resugar uu____3254  in
                        (op1, uu____3251)  in
                      FStar_Parser_AST.Op uu____3244  in
                    mk1 uu____3243
                | uu____3263 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3332 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3332 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3378 =
                   let uu____3391 =
                     let uu____3396 = resugar_pat' env pat1 branch_bv  in
                     let uu____3397 = resugar_term' env e  in
                     (uu____3396, uu____3397)  in
                   (FStar_Pervasives_Native.None, uu____3391)  in
                 [uu____3378]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3449,t1)::(pat2,uu____3452,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3548 =
            let uu____3549 =
              let uu____3556 = resugar_term' env e  in
              let uu____3557 = resugar_term' env t1  in
              let uu____3558 = resugar_term' env t2  in
              (uu____3556, uu____3557, uu____3558)  in
            FStar_Parser_AST.If uu____3549  in
          mk1 uu____3548
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3622 =
            match uu____3622 with
            | (pat,wopt,b) ->
                let uu____3664 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3664 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3716 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3716
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3720 =
            let uu____3721 =
              let uu____3736 = resugar_term' env e  in
              let uu____3737 = FStar_List.map resugar_branch branches  in
              (uu____3736, uu____3737)  in
            FStar_Parser_AST.Match uu____3721  in
          mk1 uu____3720
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3783) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____3850 =
            let uu____3851 =
              let uu____3860 = resugar_term' env e  in
              (uu____3860, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____3851  in
          mk1 uu____3850
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____3884 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____3884 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____3935 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____3935
                    in
                 let uu____3940 =
                   let uu____3945 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____3945
                    in
                 match uu____3940 with
                 | (univs1,td) ->
                     let uu____3964 =
                       let uu____3973 =
                         let uu____3974 = FStar_Syntax_Subst.compress td  in
                         uu____3974.FStar_Syntax_Syntax.n  in
                       match uu____3973 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____3985,(t1,uu____3987)::(d,uu____3989)::[])
                           -> (t1, d)
                       | uu____4032 -> failwith "wrong let binding format"
                        in
                     (match uu____3964 with
                      | (typ,def) ->
                          let uu____4067 =
                            let uu____4074 =
                              let uu____4075 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4075.FStar_Syntax_Syntax.n  in
                            match uu____4074 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4086) ->
                                let uu____4107 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4107 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4121 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4121
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4123 -> ([], def, false)  in
                          (match uu____4067 with
                           | (binders,term,is_pat_app) ->
                               let uu____4155 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4166 =
                                       let uu____4167 =
                                         let uu____4168 =
                                           let uu____4175 =
                                             bv_as_unique_ident bv  in
                                           (uu____4175,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4168
                                          in
                                       mk_pat uu____4167  in
                                     (uu____4166, term)
                                  in
                               (match uu____4155 with
                                | (pat,term1) ->
                                    let uu____4196 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4228  ->
                                                  match uu____4228 with
                                                  | (bv,q) ->
                                                      let uu____4243 =
                                                        resugar_arg_qual q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4243
                                                        (fun q1  ->
                                                           let uu____4255 =
                                                             let uu____4256 =
                                                               let uu____4263
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4263,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4256
                                                              in
                                                           mk_pat uu____4255)))
                                           in
                                        let uu____4266 =
                                          let uu____4271 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4271)
                                           in
                                        let uu____4274 =
                                          universe_to_string univs1  in
                                        (uu____4266, uu____4274)
                                      else
                                        (let uu____4280 =
                                           let uu____4285 =
                                             resugar_term' env term1  in
                                           (pat, uu____4285)  in
                                         let uu____4286 =
                                           universe_to_string univs1  in
                                         (uu____4280, uu____4286))
                                       in
                                    (attrs_opt, uu____4196))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4384 =
                   match uu____4384 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4440 =
                         let uu____4441 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4441  in
                       if uu____4440
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4516) ->
          let s =
            let uu____4542 =
              let uu____4543 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_All.pipe_right uu____4543 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4542  in
          let uu____4544 = mk1 FStar_Parser_AST.Wild  in label s uu____4544
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___72_4554 =
            match uu___72_4554 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4560,(uu____4561,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____4622 =
                        let uu____4623 =
                          let uu____4632 = resugar_seq t11  in
                          (uu____4632, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____4623  in
                      mk1 uu____4622
                  | uu____4635 -> t1  in
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
                 | uu____4681 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval  ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                let uu____4683 =
                  let uu____4684 = FStar_Syntax_Subst.compress e  in
                  uu____4684.FStar_Syntax_Syntax.n  in
                (match uu____4683 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____4688;
                        FStar_Syntax_Syntax.vars = uu____4689;_},(term,uu____4691)::[])
                     -> resugar_term' env term
                 | uu____4720 -> failwith "mutable_rval should have app term")
             in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____4758  ->
                         match uu____4758 with
                         | (x,uu____4764) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l,uu____4766,p) ->
               let uu____4768 =
                 let uu____4769 =
                   let uu____4776 = resugar_term' env e  in
                   (uu____4776, l, p)  in
                 FStar_Parser_AST.Labeled uu____4769  in
               mk1 uu____4768
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____4785 =
                 let uu____4786 =
                   let uu____4795 = resugar_term' env e  in
                   let uu____4796 =
                     let uu____4797 =
                       let uu____4798 =
                         let uu____4809 =
                           let uu____4816 =
                             let uu____4821 = resugar_term' env t1  in
                             (uu____4821, FStar_Parser_AST.Nothing)  in
                           [uu____4816]  in
                         (name1, uu____4809)  in
                       FStar_Parser_AST.Construct uu____4798  in
                     mk1 uu____4797  in
                   (uu____4795, uu____4796, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____4786  in
               mk1 uu____4785
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4839,t1) ->
               let uu____4845 =
                 let uu____4846 =
                   let uu____4855 = resugar_term' env e  in
                   let uu____4856 =
                     let uu____4857 =
                       let uu____4858 =
                         let uu____4869 =
                           let uu____4876 =
                             let uu____4881 = resugar_term' env t1  in
                             (uu____4881, FStar_Parser_AST.Nothing)  in
                           [uu____4876]  in
                         (name1, uu____4869)  in
                       FStar_Parser_AST.Construct uu____4858  in
                     mk1 uu____4857  in
                   (uu____4855, uu____4856, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____4846  in
               mk1 uu____4845
           | FStar_Syntax_Syntax.Meta_quoted (qt,uu____4899) ->
               let uu____4904 =
                 let uu____4905 = resugar_term' env qt  in
                 FStar_Parser_AST.Quote uu____4905  in
               mk1 uu____4904)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_ToSyntax_Env.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
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
               let uu____4938 = FStar_Options.print_universes ()  in
               if uu____4938
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
               let uu____4999 = FStar_Options.print_universes ()  in
               if uu____4999
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
            let uu____5040 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5040, FStar_Parser_AST.Nothing)  in
          let uu____5041 = FStar_Options.print_effect_args ()  in
          if uu____5041
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              if
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5128 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5128, (FStar_Pervasives_Native.snd post))  in
                    let uu____5137 =
                      let uu____5146 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5146 then [] else [pre]  in
                    let uu____5176 =
                      let uu____5185 =
                        let uu____5194 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5194 then [] else [pats]  in
                      FStar_List.append [post1] uu____5185  in
                    FStar_List.append uu____5137 uu____5176
                | uu____5248 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5277  ->
                   match uu____5277 with
                   | (e,uu____5287) ->
                       let uu____5288 = resugar_term' env e  in
                       (uu____5288, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___73_5309 =
              match uu___73_5309 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5342 = resugar_term' env e  in
                         (uu____5342, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5347 -> aux l tl1)
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
  FStar_ToSyntax_Env.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun b  ->
      fun r  ->
        let uu____5393 = b  in
        match uu____5393 with
        | (x,aq) ->
            let uu____5398 = resugar_arg_qual aq  in
            FStar_Util.map_opt uu____5398
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5412 =
                       let uu____5413 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5413  in
                     FStar_Parser_AST.mk_binder uu____5412 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5414 ->
                     let uu____5415 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5415
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5417 =
                          let uu____5418 =
                            let uu____5423 = bv_as_unique_ident x  in
                            (uu____5423, e)  in
                          FStar_Parser_AST.Annotated uu____5418  in
                        FStar_Parser_AST.mk_binder uu____5417 r
                          FStar_Parser_AST.Type_level imp))

and (resugar_bv_as_pat' :
  FStar_ToSyntax_Env.env ->
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
              let uu____5441 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5441  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5444 =
                if used
                then
                  let uu____5445 =
                    let uu____5452 = bv_as_unique_ident v1  in
                    (uu____5452, aqual)  in
                  FStar_Parser_AST.PatVar uu____5445
                else FStar_Parser_AST.PatWild  in
              mk1 uu____5444  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5458;
                  FStar_Syntax_Syntax.vars = uu____5459;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5469 = FStar_Options.print_bound_var_types ()  in
                if uu____5469
                then
                  let uu____5470 =
                    let uu____5471 =
                      let uu____5476 = resugar_term' env typ  in
                      (pat, uu____5476)  in
                    FStar_Parser_AST.PatAscribed uu____5471  in
                  mk1 uu____5470
                else pat

and (resugar_bv_as_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.aqual ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____5486 = resugar_arg_qual qual  in
          FStar_Util.map_opt uu____5486
            (fun aqual  ->
               let uu____5498 =
                 let uu____5503 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                   uu____5503
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5498)

and (resugar_pat' :
  FStar_ToSyntax_Env.env ->
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
          (let uu____5552 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5552) &&
            (let uu____5554 =
               FStar_List.existsML
                 (fun uu____5565  ->
                    match uu____5565 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5581)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5586 -> false
                          | uu____5587 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5554)
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
            let uu____5640 = may_drop_implicits args  in
            if uu____5640 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____5662  ->
                 match uu____5662 with
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
              ((let uu____5708 =
                  let uu____5709 =
                    let uu____5710 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____5710  in
                  Prims.op_Negation uu____5709  in
                if uu____5708
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
              let uu____5746 = filter_pattern_imp args  in
              (match uu____5746 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____5786 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____5786 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____5802 =
                       let uu____5807 =
                         let uu____5808 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____5808
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____5807)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____5802);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____5853  ->
                        match uu____5853 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____5865 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____5865)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____5869;
                 FStar_Syntax_Syntax.fv_delta = uu____5870;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____5897 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____5897 FStar_List.rev  in
              let args1 =
                let uu____5913 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____5933  ->
                          match uu____5933 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____5913 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6003 = map21 tl1 []  in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6003
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6026 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6026
                 in
              let args2 =
                let uu____6044 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6044 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6086 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6086 with
               | FStar_Pervasives_Native.Some (op,uu____6094) ->
                   mk1
                     (FStar_Parser_AST.PatOp
                        (FStar_Ident.mk_ident
                           (op,
                             ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
               | FStar_Pervasives_Native.None  ->
                   let uu____6103 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6103 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6108 ->
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
  fun uu___74_6121  ->
    match uu___74_6121 with
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
    | FStar_Syntax_Syntax.Reflectable uu____6130 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6131 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6132 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6137 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6146 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6155 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___75_6158  ->
    match uu___75_6158 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_ToSyntax_Env.env ->
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
            (tylid,uvs,bs,t,uu____6188,datacons) ->
            let uu____6198 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6225,uu____6226,uu____6227,inductive_lid,uu____6229,uu____6230)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6235 -> failwith "unexpected"))
               in
            (match uu____6198 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6254 = FStar_Options.print_implicits ()  in
                   if uu____6254 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6264 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___76_6269  ->
                             match uu___76_6269 with
                             | FStar_Syntax_Syntax.RecordType uu____6270 ->
                                 true
                             | uu____6279 -> false))
                      in
                   if uu____6264
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6327,univs1,term,uu____6330,num,uu____6332)
                           ->
                           let uu____6337 =
                             let uu____6338 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6338.FStar_Syntax_Syntax.n  in
                           (match uu____6337 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6352)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6413  ->
                                          match uu____6413 with
                                          | (b,qual) ->
                                              let uu____6428 =
                                                let uu____6429 =
                                                  bv_as_unique_ident b  in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6429
                                                 in
                                              let uu____6430 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6428, uu____6430,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6441 -> failwith "unexpected")
                       | uu____6452 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____6573,num,uu____6575) ->
                            let c =
                              let uu____6593 =
                                let uu____6596 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____6596  in
                              ((l.FStar_Ident.ident), uu____6593,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____6613 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____6689 ->
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
        let uu____6707 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6707;
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
  FStar_ToSyntax_Env.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun name  ->
      fun ts  ->
        let uu____6723 = ts  in
        match uu____6723 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____6731 =
              let uu____6732 =
                let uu____6745 =
                  let uu____6754 =
                    let uu____6761 =
                      let uu____6762 =
                        let uu____6775 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____6775)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____6762  in
                    (uu____6761, FStar_Pervasives_Native.None)  in
                  [uu____6754]  in
                (false, uu____6745)  in
              FStar_Parser_AST.Tycon uu____6732  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6731
  
let (resugar_tscheme' :
  FStar_ToSyntax_Env.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tsheme" ts 
let (resugar_eff_decl' :
  FStar_ToSyntax_Env.env ->
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
              let uu____6835 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____6835 with
              | (bs,action_defn) ->
                  let uu____6842 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____6842 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____6850 = FStar_Options.print_implicits ()
                            in
                         if uu____6850
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____6855 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____6855 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____6869 =
                             let uu____6880 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____6880,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____6869  in
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
            let uu____6954 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____6954 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____6962 = FStar_Options.print_implicits ()  in
                  if uu____6962 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____6967 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____6967 FStar_List.rev  in
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
  FStar_ToSyntax_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7027) ->
          let uu____7036 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7058 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7075 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7082 -> false
                    | uu____7097 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7036 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7129 se1 =
                 match uu____7129 with
                 | (datacon_ses1,tycons) ->
                     let uu____7155 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7155 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7170 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7170 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7205 =
                           let uu____7206 =
                             let uu____7207 =
                               let uu____7220 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, uu____7220)  in
                             FStar_Parser_AST.Tycon uu____7207  in
                           decl'_to_decl se uu____7206  in
                         FStar_Pervasives_Native.Some uu____7205
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7251,uu____7252,uu____7253,uu____7254,uu____7255)
                              ->
                              let uu____7260 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7260
                          | uu____7263 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7266 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7272) ->
          let uu____7277 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___77_7283  ->
                    match uu___77_7283 with
                    | FStar_Syntax_Syntax.Projector (uu____7284,uu____7285)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7286 -> true
                    | uu____7287 -> false))
             in
          if uu____7277
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
             | FStar_Parser_AST.Let (isrec,lets,uu____7310) ->
                 let uu____7339 =
                   let uu____7340 =
                     let uu____7341 =
                       let uu____7352 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7352)  in
                     FStar_Parser_AST.TopLevelLet uu____7341  in
                   decl'_to_decl se uu____7340  in
                 FStar_Pervasives_Native.Some uu____7339
             | uu____7389 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7393,fml) ->
          let uu____7395 =
            let uu____7396 =
              let uu____7397 =
                let uu____7402 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7402)  in
              FStar_Parser_AST.Assume uu____7397  in
            decl'_to_decl se uu____7396  in
          FStar_Pervasives_Native.Some uu____7395
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7404 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7404
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7406 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7406
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7415,t) ->
                let uu____7427 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7427
            | uu____7428 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7436,t) ->
                let uu____7448 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7448
            | uu____7449 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7473 -> failwith "Should not happen hopefully"  in
          let uu____7482 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____7482
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____7492 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7492 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____7502 = FStar_Options.print_implicits ()  in
                 if uu____7502 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____7511 =
                 let uu____7512 =
                   let uu____7513 =
                     let uu____7526 =
                       let uu____7535 =
                         let uu____7542 =
                           let uu____7543 =
                             let uu____7556 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____7556)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____7543  in
                         (uu____7542, FStar_Pervasives_Native.None)  in
                       [uu____7535]  in
                     (false, uu____7526)  in
                   FStar_Parser_AST.Tycon uu____7513  in
                 decl'_to_decl se uu____7512  in
               FStar_Pervasives_Native.Some uu____7511)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____7584 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____7584
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____7588 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___78_7594  ->
                    match uu___78_7594 with
                    | FStar_Syntax_Syntax.Projector (uu____7595,uu____7596)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7597 -> true
                    | uu____7598 -> false))
             in
          if uu____7588
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____7603 =
                 (let uu____7606 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____7606) || (FStar_List.isEmpty uvs)
                  in
               if uu____7603
               then resugar_term' env t
               else
                 (let uu____7608 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____7608 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____7616 = resugar_term' env t1  in
                      label universes uu____7616)
                in
             let uu____7617 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____7617)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7618 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____7635 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____7650 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_ToSyntax_Env.env) = FStar_ToSyntax_Env.empty_env () 
let noenv : 'a . (FStar_ToSyntax_Env.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____7666 = noenv resugar_term'  in uu____7666 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____7678 = noenv resugar_sigelt'  in uu____7678 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____7690 = noenv resugar_comp'  in uu____7690 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____7705 = noenv resugar_pat'  in uu____7705 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____7728 = noenv resugar_binder'  in uu____7728 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____7744 = noenv resugar_tscheme'  in uu____7744 ts 
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
          let uu____7765 = noenv resugar_eff_decl'  in
          uu____7765 for_free r q ed
  