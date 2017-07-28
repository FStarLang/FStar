open Prims
let doc_to_string : FStar_Pprint.document -> Prims.string =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let parser_term_to_string : FStar_Parser_AST.term -> Prims.string =
  fun t  ->
    let uu____9 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____9
  
let map_opt :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list
  =
  fun f  ->
    fun l  ->
      let uu____43 =
        FStar_Util.choose_map
          (fun uu____53  -> fun x  -> let uu____55 = f x  in ((), uu____55))
          () l
         in
      FStar_Pervasives_Native.snd uu____43
  
let bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____67 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____67
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____73 .
    ('Auu____73,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____73,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___182_127  ->
            match uu___182_127 with
            | (uu____134,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____135)) -> false
            | uu____138 -> true))
  
let label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
  
let resugar_arg_qual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option
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
  
let resugar_imp :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.imp
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        FStar_Parser_AST.Hash
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        failwith "Not an imp"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        failwith "Not an imp"
  
let rec universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____213 -> (n1, u)
  
let universe_to_string : FStar_Ident.ident Prims.list -> Prims.string =
  fun univs1  ->
    let uu____222 = FStar_Options.print_universes ()  in
    if uu____222
    then
      let uu____223 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____223 (FStar_String.concat ", ")
    else ""
  
let rec resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____256 ->
          let uu____257 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____257 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____264 =
                      let uu____265 =
                        let uu____266 =
                          let uu____277 = FStar_Util.string_of_int n1  in
                          (uu____277, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____266  in
                      FStar_Parser_AST.Const uu____265  in
                    mk1 uu____264 r
                | uu____288 ->
                    let e1 =
                      let uu____290 =
                        let uu____291 =
                          let uu____292 =
                            let uu____303 = FStar_Util.string_of_int n1  in
                            (uu____303, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____292  in
                        FStar_Parser_AST.Const uu____291  in
                      mk1 uu____290 r  in
                    let e2 = resugar_universe u1 r  in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____320 ->
               let t =
                 let uu____324 =
                   let uu____325 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____325  in
                 mk1 uu____324 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____331 =
                        let uu____332 =
                          let uu____339 = resugar_universe x r  in
                          (acc, uu____339, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____332  in
                      mk1 uu____331 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____341 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____352 =
              let uu____357 =
                let uu____358 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____358  in
              (uu____357, r)  in
            FStar_Ident.mk_ident uu____352  in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
  
let string_to_op :
  Prims.string ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun s  ->
    let name_of_op uu___183_378 =
      match uu___183_378 with
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
      | uu____465 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", (Prims.parse_int "0"))
    | uu____492 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____502 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____502 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____510 ->
               let op =
                 let uu____514 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____548) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____514
                  in
               FStar_Pervasives_Native.Some (op, (Prims.parse_int "0")))
        else FStar_Pervasives_Native.None
  
let rec resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
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
      let uu____735 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____735 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), (Prims.parse_int "0"))
      | uu____783 ->
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
                (let uu____836 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____836
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else FStar_Pervasives_Native.None)
       in
    let uu____852 =
      let uu____853 = FStar_Syntax_Subst.compress t  in
      uu____853.FStar_Syntax_Syntax.n  in
    match uu____852 with
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
        let uu____876 = string_to_op s  in
        (match uu____876 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____902 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____915 -> FStar_Pervasives_Native.None
  
let is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____924 -> false
  
let is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____929 -> true
    | uu____930 -> false
  
let rec resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un
       in
    let name a r =
      let uu____961 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Name uu____961  in
    let var a r =
      let uu____969 = FStar_Ident.lid_of_path [a] r  in
      FStar_Parser_AST.Var uu____969  in
    let uu____970 =
      let uu____971 = FStar_Syntax_Subst.compress t  in
      uu____971.FStar_Syntax_Syntax.n  in
    match uu____970 with
    | FStar_Syntax_Syntax.Tm_delayed uu____974 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____1001 =
            let uu____1004 = bv_as_unique_ident x  in [uu____1004]  in
          FStar_Ident.lid_of_ids uu____1001  in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____1007 =
            let uu____1010 = bv_as_unique_ident x  in [uu____1010]  in
          FStar_Ident.lid_of_ids uu____1007  in
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
          let uu____1028 =
            let uu____1029 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
            FStar_Parser_AST.Discrim uu____1029  in
          mk1 uu____1028
        else
          if
            FStar_Util.starts_with s FStar_Syntax_Util.field_projector_prefix
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
             | uu____1039 -> failwith "wrong projector format")
          else
            (let uu____1043 =
               ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                 ||
                 (let uu____1046 =
                    let uu____1047 = FStar_String.get s (Prims.parse_int "0")
                       in
                    FStar_Char.uppercase uu____1047  in
                  let uu____1048 = FStar_String.get s (Prims.parse_int "0")
                     in
                  uu____1046 <> uu____1048)
                in
             if uu____1043
             then
               let uu____1049 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos  in
               mk1 uu____1049
             else
               (let uu____1051 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos  in
                mk1 uu____1051))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____1058 = FStar_Options.print_universes ()  in
        if uu____1058
        then
          let e1 = resugar_term e  in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____1065 =
                   let uu____1066 =
                     let uu____1073 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos  in
                     (acc, uu____1073, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1066  in
                 mk1 uu____1065) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1076 = FStar_Syntax_Syntax.is_teff t  in
        if uu____1076
        then
          let uu____1077 = name "Effect" t.FStar_Syntax_Syntax.pos  in
          mk1 uu____1077
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____1080 = name "Type0" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____1080
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____1081 = name "Type" t.FStar_Syntax_Syntax.pos  in
             mk1 uu____1081
         | uu____1082 ->
             let uu____1083 = FStar_Options.print_universes ()  in
             if uu____1083
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos  in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos
                  in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____1101 = name "Type" t.FStar_Syntax_Syntax.pos  in
                mk1 uu____1101))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1104) ->
        let uu____1125 = FStar_Syntax_Subst.open_term xs body  in
        (match uu____1125 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1133 = FStar_Options.print_implicits ()  in
               if uu____1133 then xs1 else filter_imp xs1  in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____1147  ->
                       match uu____1147 with
                       | (x,qual) -> resugar_bv_as_pat x qual))
                in
             let body2 = resugar_term body1  in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____1177 = FStar_Syntax_Subst.open_comp xs body  in
        (match uu____1177 with
         | (xs1,body1) ->
             let xs2 =
               let uu____1185 = FStar_Options.print_implicits ()  in
               if uu____1185 then xs1 else filter_imp xs1  in
             let body2 = resugar_comp body1  in
             let xs3 =
               let uu____1191 =
                 FStar_All.pipe_right xs2
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos))
                  in
               FStar_All.pipe_right uu____1191 FStar_List.rev  in
             let rec aux body3 uu___184_1210 =
               match uu___184_1210 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3))
                      in
                   aux body4 tl1
                in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____1226 =
          let uu____1231 =
            let uu____1232 = FStar_Syntax_Syntax.mk_binder x  in [uu____1232]
             in
          FStar_Syntax_Subst.open_term uu____1231 phi  in
        (match uu____1226 with
         | (x1,phi1) ->
             let b =
               let uu____1236 =
                 let uu____1239 = FStar_List.hd x1  in
                 resugar_binder uu____1239 t.FStar_Syntax_Syntax.pos  in
               FStar_Util.must uu____1236  in
             let uu____1244 =
               let uu____1245 =
                 let uu____1250 = resugar_term phi1  in (b, uu____1250)  in
               FStar_Parser_AST.Refine uu____1245  in
             mk1 uu____1244)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___185_1292 =
          match uu___185_1292 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____1362 -> failwith "last of an empty list"  in
        let rec last_two uu___186_1398 =
          match uu___186_1398 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____1429::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____1506::t1 -> last_two t1  in
        let rec last_three uu___187_1547 =
          match uu___187_1547 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1578::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1605::uu____1606::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1714::t1 -> last_three t1  in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1800  ->
                    match uu____1800 with
                    | (e2,qual) ->
                        let uu____1819 = resugar_term e2  in
                        (uu____1819, qual)))
             in
          let e2 = resugar_term e1  in
          FStar_List.fold_left
            (fun acc  ->
               fun uu____1835  ->
                 match uu____1835 with
                 | (x,qual) ->
                     let uu____1848 =
                       let uu____1849 =
                         let uu____1856 = resugar_imp qual  in
                         (acc, x, uu____1856)  in
                       FStar_Parser_AST.App uu____1849  in
                     mk1 uu____1848) e2 args2
           in
        let args1 =
          let uu____1866 = FStar_Options.print_implicits ()  in
          if uu____1866 then args else filter_imp args  in
        let uu____1878 = resugar_term_as_op e  in
        (match uu____1878 with
         | FStar_Pervasives_Native.None  -> resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("tuple",uu____1889) ->
             (match args1 with
              | (fst1,uu____1895)::(snd1,uu____1897)::rest ->
                  let e1 =
                    let uu____1928 =
                      let uu____1929 =
                        let uu____1936 =
                          let uu____1939 = resugar_term fst1  in
                          let uu____1940 =
                            let uu____1943 = resugar_term snd1  in
                            [uu____1943]  in
                          uu____1939 :: uu____1940  in
                        ((FStar_Ident.id_of_text "*"), uu____1936)  in
                      FStar_Parser_AST.Op uu____1929  in
                    mk1 uu____1928  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1956  ->
                         match uu____1956 with
                         | (x,uu____1962) ->
                             let uu____1963 =
                               let uu____1964 =
                                 let uu____1971 =
                                   let uu____1974 =
                                     let uu____1977 = resugar_term x  in
                                     [uu____1977]  in
                                   e1 :: uu____1974  in
                                 ((FStar_Ident.id_of_text "*"), uu____1971)
                                  in
                               FStar_Parser_AST.Op uu____1964  in
                             mk1 uu____1963) e1 rest
              | uu____1980 -> resugar_as_app e args1)
         | FStar_Pervasives_Native.Some ("dtuple",uu____1989) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1  in
             let body =
               match args2 with
               | (b,uu____2015)::[] -> b
               | uu____2032 -> failwith "wrong arguments to dtuple"  in
             let uu____2043 =
               let uu____2044 = FStar_Syntax_Subst.compress body  in
               uu____2044.FStar_Syntax_Syntax.n  in
             (match uu____2043 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2049) ->
                  let uu____2070 = FStar_Syntax_Subst.open_term xs body1  in
                  (match uu____2070 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____2078 = FStar_Options.print_implicits ()
                            in
                         if uu____2078 then xs1 else filter_imp xs1  in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (map_opt
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos))
                          in
                       let body3 = resugar_term body2  in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____2090 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____2111  ->
                            match uu____2111 with
                            | (e1,qual) -> resugar_term e1))
                     in
                  let e1 = resugar_term e  in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | FStar_Pervasives_Native.Some ("dtuple",uu____2123) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (ref_read,uu____2129) when
             ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
             let uu____2134 = FStar_List.hd args1  in
             (match uu____2134 with
              | (t1,uu____2148) ->
                  let uu____2153 =
                    let uu____2154 = FStar_Syntax_Subst.compress t1  in
                    uu____2154.FStar_Syntax_Syntax.n  in
                  (match uu____2153 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____2159 =
                         let uu____2160 =
                           let uu____2165 = resugar_term t1  in
                           (uu____2165, f)  in
                         FStar_Parser_AST.Project uu____2160  in
                       mk1 uu____2159
                   | uu____2166 -> resugar_term t1))
         | FStar_Pervasives_Native.Some ("try_with",uu____2167) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1  in
             let uu____2187 =
               match new_args with
               | (a1,uu____2205)::(a2,uu____2207)::[] -> (a1, a2)
               | uu____2238 -> failwith "wrong arguments to try_with"  in
             (match uu____2187 with
              | (body,handler) ->
                  let decomp term =
                    let uu____2269 =
                      let uu____2270 = FStar_Syntax_Subst.compress term  in
                      uu____2270.FStar_Syntax_Syntax.n  in
                    match uu____2269 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2275) ->
                        let uu____2296 = FStar_Syntax_Subst.open_term x e1
                           in
                        (match uu____2296 with | (x1,e2) -> e2)
                    | uu____2303 ->
                        failwith "wrong argument format to try_with"
                     in
                  let body1 =
                    let uu____2305 = decomp body  in resugar_term uu____2305
                     in
                  let handler1 =
                    let uu____2307 = decomp handler  in
                    resugar_term uu____2307  in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____2313,uu____2314,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____2346,uu____2347,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____2368 =
                          let uu____2369 =
                            let uu____2378 = resugar_body t11  in
                            (uu____2378, t2, t3)  in
                          FStar_Parser_AST.Ascribed uu____2369  in
                        mk1 uu____2368
                    | uu____2381 ->
                        failwith "unexpected body format to try_with"
                     in
                  let e1 = resugar_body body1  in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____2436 -> []  in
                  let branches = resugar_branches handler1  in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | FStar_Pervasives_Native.Some ("try_with",uu____2466) ->
             resugar_as_app e args1
         | FStar_Pervasives_Native.Some (op,uu____2472) when
             (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____2557 -> (xs, pat, t1)  in
             let resugar body =
               let uu____2568 =
                 let uu____2569 = FStar_Syntax_Subst.compress body  in
                 uu____2569.FStar_Syntax_Syntax.n  in
               match uu____2568 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2574) ->
                   let uu____2595 = FStar_Syntax_Subst.open_term xs body1  in
                   (match uu____2595 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____2603 = FStar_Options.print_implicits ()
                             in
                          if uu____2603 then xs1 else filter_imp xs1  in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (map_opt
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos))
                           in
                        let uu____2612 =
                          let uu____2621 =
                            let uu____2622 =
                              FStar_Syntax_Subst.compress body2  in
                            uu____2622.FStar_Syntax_Syntax.n  in
                          match uu____2621 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1  in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____2691  ->
                                                 match uu____2691 with
                                                 | (e2,uu____2697) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____2700) ->
                                    let uu____2701 =
                                      let uu____2704 =
                                        let uu____2705 = name s r  in
                                        mk1 uu____2705  in
                                      [uu____2704]  in
                                    [uu____2701]
                                | uu____2710 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists"
                                 in
                              (pats, body3)
                          | uu____2719 ->
                              let uu____2720 = resugar_term body2  in
                              ([], uu____2720)
                           in
                        (match uu____2612 with
                         | (pats,body3) ->
                             let uu____2737 = uncurry xs3 pats body3  in
                             (match uu____2737 with
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
               | uu____2785 ->
                   if op = "forall"
                   then
                     let uu____2786 =
                       let uu____2787 =
                         let uu____2800 = resugar_term body  in
                         ([], [[]], uu____2800)  in
                       FStar_Parser_AST.QForall uu____2787  in
                     mk1 uu____2786
                   else
                     (let uu____2812 =
                        let uu____2813 =
                          let uu____2826 = resugar_term body  in
                          ([], [[]], uu____2826)  in
                        FStar_Parser_AST.QExists uu____2813  in
                      mk1 uu____2812)
                in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1  in
               (match args2 with
                | (b,uu____2853)::[] -> resugar b
                | uu____2870 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | FStar_Pervasives_Native.Some ("alloc",uu____2880) ->
             let uu____2885 = FStar_List.hd args1  in
             (match uu____2885 with | (e1,uu____2899) -> resugar_term e1)
         | FStar_Pervasives_Native.Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op  in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____2944  ->
                       match uu____2944 with | (e1,qual) -> resugar_term e1))
                in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____2951 =
                    FStar_Parser_ToDocument.handleable_args_length op1  in
                  (match uu____2951 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____2958 =
                         let uu____2959 =
                           let uu____2966 =
                             let uu____2969 = last1 args1  in
                             resugar uu____2969  in
                           (op1, uu____2966)  in
                         FStar_Parser_AST.Op uu____2959  in
                       mk1 uu____2958
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____2984 =
                         let uu____2985 =
                           let uu____2992 =
                             let uu____2995 = last_two args1  in
                             resugar uu____2995  in
                           (op1, uu____2992)  in
                         FStar_Parser_AST.Op uu____2985  in
                       mk1 uu____2984
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____3010 =
                         let uu____3011 =
                           let uu____3018 =
                             let uu____3021 = last_three args1  in
                             resugar uu____3021  in
                           (op1, uu____3018)  in
                         FStar_Parser_AST.Op uu____3011  in
                       mk1 uu____3010
                   | uu____3030 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____3037 =
                    let uu____3038 =
                      let uu____3045 =
                        let uu____3048 = last_two args1  in
                        resugar uu____3048  in
                      (op1, uu____3045)  in
                    FStar_Parser_AST.Op uu____3038  in
                  mk1 uu____3037
              | uu____3057 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____3060,t1)::[]) ->
        let bnds =
          let uu____3133 =
            let uu____3138 = resugar_pat pat  in
            let uu____3139 = resugar_term e  in (uu____3138, uu____3139)  in
          [uu____3133]  in
        let body = resugar_term t1  in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____3157,t1)::(pat2,uu____3160,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____3256 =
          let uu____3257 =
            let uu____3264 = resugar_term e  in
            let uu____3265 = resugar_term t1  in
            let uu____3266 = resugar_term t2  in
            (uu____3264, uu____3265, uu____3266)  in
          FStar_Parser_AST.If uu____3257  in
        mk1 uu____3256
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____3324 =
          match uu____3324 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat  in
              let wopt1 =
                match wopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some e1 ->
                    let uu____3355 = resugar_term e1  in
                    FStar_Pervasives_Native.Some uu____3355
                 in
              let b1 = resugar_term b  in (pat1, wopt1, b1)
           in
        let uu____3359 =
          let uu____3360 =
            let uu____3375 = resugar_term e  in
            let uu____3376 = FStar_List.map resugar_branch branches  in
            (uu____3375, uu____3376)  in
          FStar_Parser_AST.Match uu____3360  in
        mk1 uu____3359
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3416) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1  in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt  in
        let uu____3483 =
          let uu____3484 =
            let uu____3493 = resugar_term e  in (uu____3493, term, tac_opt1)
             in
          FStar_Parser_AST.Ascribed uu____3484  in
        mk1 uu____3483
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
        let uu____3517 = FStar_Syntax_Subst.open_let_rec bnds body  in
        (match uu____3517 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____3542 =
                 let uu____3547 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef
                    in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____3547
                  in
               match uu____3542 with
               | (univs1,td) ->
                   let uu____3558 =
                     let uu____3567 =
                       let uu____3568 = FStar_Syntax_Subst.compress td  in
                       uu____3568.FStar_Syntax_Syntax.n  in
                     match uu____3567 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____3579,(t1,uu____3581)::(d,uu____3583)::[]) ->
                         (t1, d)
                     | uu____3626 -> failwith "wrong let binding format"  in
                   (match uu____3558 with
                    | (typ,def) ->
                        let uu____3653 =
                          let uu____3660 =
                            let uu____3661 = FStar_Syntax_Subst.compress def
                               in
                            uu____3661.FStar_Syntax_Syntax.n  in
                          match uu____3660 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____3672) ->
                              let uu____3693 =
                                FStar_Syntax_Subst.open_term b t1  in
                              (match uu____3693 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____3707 =
                                       FStar_Options.print_implicits ()  in
                                     if uu____3707 then b1 else filter_imp b1
                                      in
                                   (b2, t2, true))
                          | uu____3709 -> ([], def, false)  in
                        (match uu____3653 with
                         | (binders,term,is_pat_app) ->
                             let uu____3733 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____3744 =
                                     let uu____3745 =
                                       let uu____3746 =
                                         let uu____3753 =
                                           bv_as_unique_ident bv  in
                                         (uu____3753,
                                           FStar_Pervasives_Native.None)
                                          in
                                       FStar_Parser_AST.PatVar uu____3746  in
                                     mk_pat uu____3745  in
                                   (uu____3744, term)
                                in
                             (match uu____3733 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (map_opt
                                           (fun uu____3789  ->
                                              match uu____3789 with
                                              | (bv,q) ->
                                                  let uu____3804 =
                                                    resugar_arg_qual q  in
                                                  FStar_Util.map_opt
                                                    uu____3804
                                                    (fun q1  ->
                                                       let uu____3816 =
                                                         let uu____3817 =
                                                           let uu____3824 =
                                                             bv_as_unique_ident
                                                               bv
                                                              in
                                                           (uu____3824, q1)
                                                            in
                                                         FStar_Parser_AST.PatVar
                                                           uu____3817
                                                          in
                                                       mk_pat uu____3816)))
                                       in
                                    let uu____3827 =
                                      let uu____3832 = resugar_term term1  in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____3832)
                                       in
                                    let uu____3835 =
                                      universe_to_string univs1  in
                                    (uu____3827, uu____3835)
                                  else
                                    (let uu____3841 =
                                       let uu____3846 = resugar_term term1
                                          in
                                       (pat, uu____3846)  in
                                     let uu____3847 =
                                       universe_to_string univs1  in
                                     (uu____3841, uu____3847)))))
                in
             let r = FStar_List.map resugar_one_binding bnds1  in
             let bnds2 =
               let f =
                 let uu____3893 =
                   let uu____3894 = FStar_Options.print_universes ()  in
                   Prims.op_Negation uu____3894  in
                 if uu____3893
                 then FStar_Pervasives_Native.fst
                 else
                   (fun uu___188_3914  ->
                      match uu___188_3914 with
                      | ((pat,body2),univs1) -> (pat, (label univs1 body2)))
                  in
               FStar_List.map f r  in
             let body2 = resugar_term body1  in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____3955) ->
        let s =
          let uu____3981 =
            let uu____3982 = FStar_Syntax_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____3982 FStar_Util.string_of_int  in
          Prims.strcat "?u" uu____3981  in
        let uu____3983 = mk1 FStar_Parser_AST.Wild  in label s uu____3983
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___189_3993 =
          match uu___189_3993 with
          | FStar_Syntax_Syntax.Data_app  ->
              let rec head_fv_universes_args h =
                let uu____4014 =
                  let uu____4015 = FStar_Syntax_Subst.compress h  in
                  uu____4015.FStar_Syntax_Syntax.n  in
                match uu____4014 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu____4035 = FStar_Syntax_Syntax.lid_of_fv fv  in
                    (uu____4035, [], [])
                | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                    let uu____4058 = head_fv_universes_args h1  in
                    (match uu____4058 with
                     | (h2,uvs,args) -> (h2, (FStar_List.append uvs u), args))
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let uu____4146 = head_fv_universes_args head1  in
                    (match uu____4146 with
                     | (h1,uvs,args') ->
                         (h1, uvs, (FStar_List.append args' args)))
                | uu____4218 ->
                    let uu____4219 =
                      let uu____4220 =
                        let uu____4221 =
                          let uu____4222 = resugar_term h  in
                          parser_term_to_string uu____4222  in
                        FStar_Util.format1 "Not an application or a fv %s"
                          uu____4221
                         in
                      FStar_Errors.Err uu____4220  in
                    FStar_Exn.raise uu____4219
                 in
              let uu____4239 =
                try
                  let uu____4291 = FStar_Syntax_Util.unmeta e  in
                  head_fv_universes_args uu____4291
                with
                | FStar_Errors.Err uu____4312 ->
                    let uu____4313 =
                      let uu____4314 =
                        let uu____4319 =
                          let uu____4320 =
                            let uu____4321 = resugar_term e  in
                            parser_term_to_string uu____4321  in
                          FStar_Util.format1 "wrong Data_app head format %s"
                            uu____4320
                           in
                        (uu____4319, (e.FStar_Syntax_Syntax.pos))  in
                      FStar_Errors.Error uu____4314  in
                    FStar_Exn.raise uu____4313
                 in
              (match uu____4239 with
               | (head1,universes,args) ->
                   let universes1 =
                     FStar_List.map
                       (fun u  ->
                          let uu____4375 =
                            resugar_universe u t.FStar_Syntax_Syntax.pos  in
                          (uu____4375, FStar_Parser_AST.UnivApp)) universes
                      in
                   let args1 =
                     FStar_List.map
                       (fun uu____4398  ->
                          match uu____4398 with
                          | (t1,q) ->
                              let uu____4415 = resugar_term t1  in
                              let uu____4416 = resugar_imp q  in
                              (uu____4415, uu____4416)) args
                      in
                   let args2 =
                     let uu____4424 =
                       (FStar_Parser_Const.is_tuple_data_lid' head1) ||
                         (let uu____4426 = FStar_Options.print_universes ()
                             in
                          Prims.op_Negation uu____4426)
                        in
                     if uu____4424
                     then args1
                     else FStar_List.append universes1 args1  in
                   mk1 (FStar_Parser_AST.Construct (head1, args2)))
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e  in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____4449,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____4474 =
                      let uu____4475 =
                        let uu____4484 = resugar_seq t11  in
                        (uu____4484, t2, t3)  in
                      FStar_Parser_AST.Ascribed uu____4475  in
                    mk1 uu____4474
                | uu____4487 -> t1  in
              resugar_seq term
          | FStar_Syntax_Syntax.Primop  -> resugar_term e
          | FStar_Syntax_Syntax.Masked_effect  -> resugar_term e
          | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term e
          | FStar_Syntax_Syntax.Mutable_alloc  ->
              let term = resugar_term e  in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier ,l,t1)
                   ->
                   mk1
                     (FStar_Parser_AST.Let (FStar_Parser_AST.Mutable, l, t1))
               | uu____4509 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____4511 =
                let uu____4512 = FStar_Syntax_Subst.compress e  in
                uu____4512.FStar_Syntax_Syntax.n  in
              (match uu____4511 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.pos = uu____4516;
                      FStar_Syntax_Syntax.vars = uu____4517;_},(term,uu____4519)::[])
                   -> resugar_term term
               | uu____4548 -> failwith "mutable_rval should have app term")
           in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____4586  ->
                       match uu____4586 with
                       | (x,uu____4592) -> resugar_term x))
                in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____4594,p) ->
             let uu____4596 =
               let uu____4597 =
                 let uu____4604 = resugar_term e  in (uu____4604, l, p)  in
               FStar_Parser_AST.Labeled uu____4597  in
             mk1 uu____4596
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____4606,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____4615 =
               let uu____4616 =
                 let uu____4625 = resugar_term e  in
                 let uu____4626 =
                   let uu____4627 =
                     let uu____4628 =
                       let uu____4639 =
                         let uu____4646 =
                           let uu____4651 = resugar_term t1  in
                           (uu____4651, FStar_Parser_AST.Nothing)  in
                         [uu____4646]  in
                       (name1, uu____4639)  in
                     FStar_Parser_AST.Construct uu____4628  in
                   mk1 uu____4627  in
                 (uu____4625, uu____4626, FStar_Pervasives_Native.None)  in
               FStar_Parser_AST.Ascribed uu____4616  in
             mk1 uu____4615
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4669,t1) ->
             let uu____4675 =
               let uu____4676 =
                 let uu____4685 = resugar_term e  in
                 let uu____4686 =
                   let uu____4687 =
                     let uu____4688 =
                       let uu____4699 =
                         let uu____4706 =
                           let uu____4711 = resugar_term t1  in
                           (uu____4711, FStar_Parser_AST.Nothing)  in
                         [uu____4706]  in
                       (name1, uu____4699)  in
                     FStar_Parser_AST.Construct uu____4688  in
                   mk1 uu____4687  in
                 (uu____4685, uu____4686, FStar_Pervasives_Native.None)  in
               FStar_Parser_AST.Ascribed uu____4676  in
             mk1 uu____4675)
    | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term =
  fun c  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (typ,u) ->
        let t = resugar_term typ  in
        (match u with
         | FStar_Pervasives_Native.None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Parser_Const.effect_Tot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | FStar_Pervasives_Native.Some u1 ->
             let uu____4759 = FStar_Options.print_universes ()  in
             if uu____4759
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
        let t = resugar_term typ  in
        (match u with
         | FStar_Pervasives_Native.None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Parser_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | FStar_Pervasives_Native.Some u1 ->
             let uu____4820 = FStar_Options.print_universes ()  in
             if uu____4820
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
          let uu____4861 = resugar_term c1.FStar_Syntax_Syntax.result_typ  in
          (uu____4861, FStar_Parser_AST.Nothing)  in
        let uu____4862 = FStar_Options.print_effect_args ()  in
        if uu____4862
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
              let rec aux l uu___190_4919 =
                match uu___190_4919 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____4980 -> aux l tl1
                     | uu____4987 -> aux ((t, aq) :: l) tl1)
                 in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args  in
          let args1 =
            FStar_List.map
              (fun uu____5022  ->
                 match uu____5022 with
                 | (e,uu____5032) ->
                     let uu____5033 = resugar_term e  in
                     (uu____5033, FStar_Parser_AST.Nothing)) args
             in
          let rec aux l uu___191_5054 =
            match uu___191_5054 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____5087 = resugar_term e  in
                       (uu____5087, FStar_Parser_AST.Nothing)  in
                     aux (e1 :: l) tl1
                 | uu____5092 -> aux l tl1)
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

and resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option
  =
  fun b  ->
    fun r  ->
      let uu____5137 = b  in
      match uu____5137 with
      | (x,aq) ->
          let uu____5142 = resugar_arg_qual aq  in
          FStar_Util.map_opt uu____5142
            (fun imp  ->
               let e = resugar_term x.FStar_Syntax_Syntax.sort  in
               match e.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Wild  ->
                   let uu____5156 =
                     let uu____5157 = bv_as_unique_ident x  in
                     FStar_Parser_AST.Variable uu____5157  in
                   FStar_Parser_AST.mk_binder uu____5156 r
                     FStar_Parser_AST.Type_level imp
               | uu____5158 ->
                   let uu____5159 = FStar_Syntax_Syntax.is_null_bv x  in
                   if uu____5159
                   then
                     FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                       FStar_Parser_AST.Type_level imp
                   else
                     (let uu____5161 =
                        let uu____5162 =
                          let uu____5167 = bv_as_unique_ident x  in
                          (uu____5167, e)  in
                        FStar_Parser_AST.Annotated uu____5162  in
                      FStar_Parser_AST.mk_binder uu____5161 r
                        FStar_Parser_AST.Type_level imp))

and resugar_bv_as_pat :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual ->
      FStar_Parser_AST.pattern FStar_Pervasives_Native.option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____5176 = FStar_Syntax_Syntax.range_of_bv x  in
        FStar_Parser_AST.mk_pattern a uu____5176  in
      let uu____5177 =
        let uu____5178 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
        uu____5178.FStar_Syntax_Syntax.n  in
      match uu____5177 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix
             in
          if i = (Prims.parse_int "0")
          then
            let uu____5186 = mk1 FStar_Parser_AST.PatWild  in
            FStar_Pervasives_Native.Some uu____5186
          else
            (let uu____5188 = resugar_arg_qual qual  in
             FStar_Util.bind_opt uu____5188
               (fun aq  ->
                  let uu____5200 =
                    let uu____5201 =
                      let uu____5202 =
                        let uu____5209 = bv_as_unique_ident x  in
                        (uu____5209, aq)  in
                      FStar_Parser_AST.PatVar uu____5202  in
                    mk1 uu____5201  in
                  FStar_Pervasives_Native.Some uu____5200))
      | uu____5212 ->
          let uu____5213 = resugar_arg_qual qual  in
          FStar_Util.bind_opt uu____5213
            (fun aq  ->
               let pat =
                 let uu____5228 =
                   let uu____5229 =
                     let uu____5236 = bv_as_unique_ident x  in
                     (uu____5236, aq)  in
                   FStar_Parser_AST.PatVar uu____5229  in
                 mk1 uu____5228  in
               let uu____5239 = FStar_Options.print_bound_var_types ()  in
               if uu____5239
               then
                 let uu____5242 =
                   let uu____5243 =
                     let uu____5244 =
                       let uu____5249 =
                         resugar_term x.FStar_Syntax_Syntax.sort  in
                       (pat, uu____5249)  in
                     FStar_Parser_AST.PatAscribed uu____5244  in
                   mk1 uu____5243  in
                 FStar_Pervasives_Native.Some uu____5242
               else FStar_Pervasives_Native.Some pat)

and resugar_pat : FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
    let to_arg_qual bopt =
      FStar_Util.bind_opt bopt
        (fun b  ->
           if true
           then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
           else FStar_Pervasives_Native.None)
       in
    let rec aux p1 imp_opt =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
      | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
          mk1
            (FStar_Parser_AST.PatName
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          FStar_Ident.lid_equals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.cons_lid
          ->
          let args1 =
            FStar_List.map
              (fun uu____5326  ->
                 match uu____5326 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args
             in
          mk1 (FStar_Parser_AST.PatList args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          (FStar_Parser_Const.is_tuple_data_lid'
             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
            ||
            (FStar_Parser_Const.is_dtuple_data_lid'
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
          ->
          let args1 =
            FStar_List.map
              (fun uu____5361  ->
                 match uu____5361 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args
             in
          let uu____5368 =
            FStar_Parser_Const.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          if uu____5368
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____5374;
             FStar_Syntax_Syntax.fv_delta = uu____5375;
             FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____5402 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
               in
            FStar_All.pipe_right uu____5402 FStar_List.rev  in
          let args1 =
            let uu____5418 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5438  ->
                      match uu____5438 with
                      | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
               in
            FStar_All.pipe_right uu____5418 FStar_List.rev  in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____5508 = map21 tl1 []  in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____5508
            | (hd1::tl1,hd2::tl2) ->
                let uu____5531 = map21 tl1 tl2  in (hd1, hd2) :: uu____5531
             in
          let args2 =
            let uu____5549 = map21 fields1 args1  in
            FStar_All.pipe_right uu____5549 FStar_List.rev  in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____5600  ->
                 match uu____5600 with
                 | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)) args
             in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____5610 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
             in
          (match uu____5610 with
           | FStar_Pervasives_Native.Some (op,uu____5618) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | FStar_Pervasives_Native.None  ->
               let uu____5627 =
                 let uu____5628 =
                   let uu____5635 = bv_as_unique_ident v1  in
                   let uu____5636 = to_arg_qual imp_opt  in
                   (uu____5635, uu____5636)  in
                 FStar_Parser_AST.PatVar uu____5628  in
               mk1 uu____5627)
      | FStar_Syntax_Syntax.Pat_wild uu____5641 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____5649 =
              let uu____5650 =
                let uu____5657 = bv_as_unique_ident bv  in
                (uu____5657,
                  (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))
                 in
              FStar_Parser_AST.PatVar uu____5650  in
            mk1 uu____5649  in
          let uu____5660 = FStar_Options.print_bound_var_types ()  in
          if uu____5660
          then
            let uu____5661 =
              let uu____5662 =
                let uu____5667 = resugar_term term  in (pat, uu____5667)  in
              FStar_Parser_AST.PatAscribed uu____5662  in
            mk1 uu____5661
          else pat
       in
    aux p FStar_Pervasives_Native.None

let resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option
  =
  fun uu___192_5674  ->
    match uu___192_5674 with
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
    | FStar_Syntax_Syntax.Reflectable uu____5683 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____5684 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____5685 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____5690 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____5699 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____5708 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___193_5712  ->
    match uu___193_5712 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let resugar_typ :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelts,FStar_Parser_AST.tycon)
        FStar_Pervasives_Native.tuple2
  =
  fun datacon_ses  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tylid,uvs,bs,t,uu____5741,datacons) ->
          let uu____5751 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____5778,uu____5779,uu____5780,inductive_lid,uu____5782,uu____5783)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____5788 -> failwith "unexpected"))
             in
          (match uu____5751 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____5807 = FStar_Options.print_implicits ()  in
                 if uu____5807 then bs else filter_imp bs  in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (map_opt
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos))
                  in
               let tyc =
                 let uu____5817 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___194_5822  ->
                           match uu___194_5822 with
                           | FStar_Syntax_Syntax.RecordType uu____5823 ->
                               true
                           | uu____5832 -> false))
                    in
                 if uu____5817
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____5880,univs1,term,uu____5883,num,uu____5885)
                         ->
                         let uu____5890 =
                           let uu____5891 = FStar_Syntax_Subst.compress term
                              in
                           uu____5891.FStar_Syntax_Syntax.n  in
                         (match uu____5890 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____5905) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____5966  ->
                                        match uu____5966 with
                                        | (b,qual) ->
                                            let uu____5981 =
                                              let uu____5982 =
                                                bv_as_unique_ident b  in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____5982
                                               in
                                            let uu____5983 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort
                                               in
                                            (uu____5981, uu____5983,
                                              FStar_Pervasives_Native.None)))
                                 in
                              FStar_List.append mfields fields
                          | uu____5994 -> failwith "unexpected")
                     | uu____6005 -> failwith "unexpected"  in
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
                          (l,univs1,term,uu____6126,num,uu____6128) ->
                          let c =
                            let uu____6146 =
                              let uu____6149 = resugar_term term  in
                              FStar_Pervasives_Native.Some uu____6149  in
                            ((l.FStar_Ident.ident), uu____6146,
                              FStar_Pervasives_Native.None, false)
                             in
                          c :: constructors
                      | uu____6166 -> failwith "unexpected"  in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons
                       in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2,
                        FStar_Pervasives_Native.None, constructors))
                  in
               (other_datacons, tyc))
      | uu____6242 ->
          failwith
            "Impossible : only Sig_inductive_typ can be resugared as types"
  
let mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____6263 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6263;
          FStar_Parser_AST.attrs = []
        }
  
let decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let resugar_tscheme' :
  Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun name  ->
    fun ts  ->
      let uu____6280 = ts  in
      match uu____6280 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
          let uu____6288 =
            let uu____6289 =
              let uu____6302 =
                let uu____6311 =
                  let uu____6318 =
                    let uu____6319 =
                      let uu____6332 = resugar_term typ  in
                      (name1, [], FStar_Pervasives_Native.None, uu____6332)
                       in
                    FStar_Parser_AST.TyconAbbrev uu____6319  in
                  (uu____6318, FStar_Pervasives_Native.None)  in
                [uu____6311]  in
              (false, uu____6302)  in
            FStar_Parser_AST.Tycon uu____6289  in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6288
  
let resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun ts  -> resugar_tscheme' "tsheme" ts 
let resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let resugar_action d for_free1 =
            let action_params =
              FStar_Syntax_Subst.open_binders
                d.FStar_Syntax_Syntax.action_params
               in
            let uu____6391 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn
               in
            match uu____6391 with
            | (bs,action_defn) ->
                let uu____6398 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ
                   in
                (match uu____6398 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____6406 = FStar_Options.print_implicits ()  in
                       if uu____6406
                       then action_params
                       else filter_imp action_params  in
                     let action_params2 =
                       let uu____6411 =
                         FStar_All.pipe_right action_params1
                           (map_opt (fun b  -> resugar_binder b r))
                          in
                       FStar_All.pipe_right uu____6411 FStar_List.rev  in
                     let action_defn1 = resugar_term action_defn  in
                     let action_typ1 = resugar_term action_typ  in
                     if for_free1
                     then
                       let a =
                         let uu____6425 =
                           let uu____6436 =
                             FStar_Ident.lid_of_str "construct"  in
                           (uu____6436,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)])
                            in
                         FStar_Parser_AST.Construct uu____6425  in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un  in
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
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident  in
          let uu____6510 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature
             in
          match uu____6510 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____6518 = FStar_Options.print_implicits ()  in
                if uu____6518 then eff_binders else filter_imp eff_binders
                 in
              let eff_binders2 =
                let uu____6523 =
                  FStar_All.pipe_right eff_binders1
                    (map_opt (fun b  -> resugar_binder b r))
                   in
                FStar_All.pipe_right uu____6523 FStar_List.rev  in
              let eff_typ1 = resugar_term eff_typ  in
              let ret_wp =
                resugar_tscheme' "ret_wp" ed.FStar_Syntax_Syntax.ret_wp  in
              let bind_wp =
                resugar_tscheme' "bind_wp" ed.FStar_Syntax_Syntax.ret_wp  in
              let if_then_else1 =
                resugar_tscheme' "if_then_else"
                  ed.FStar_Syntax_Syntax.if_then_else
                 in
              let ite_wp =
                resugar_tscheme' "ite_wp" ed.FStar_Syntax_Syntax.ite_wp  in
              let stronger =
                resugar_tscheme' "stronger" ed.FStar_Syntax_Syntax.stronger
                 in
              let close_wp =
                resugar_tscheme' "close_wp" ed.FStar_Syntax_Syntax.close_wp
                 in
              let assert_p =
                resugar_tscheme' "assert_p" ed.FStar_Syntax_Syntax.assert_p
                 in
              let assume_p =
                resugar_tscheme' "assume_p" ed.FStar_Syntax_Syntax.assume_p
                 in
              let null_wp =
                resugar_tscheme' "null_wp" ed.FStar_Syntax_Syntax.null_wp  in
              let trivial =
                resugar_tscheme' "trivial" ed.FStar_Syntax_Syntax.trivial  in
              let repr =
                resugar_tscheme' "repr" ([], (ed.FStar_Syntax_Syntax.repr))
                 in
              let return_repr =
                resugar_tscheme' "return_repr"
                  ed.FStar_Syntax_Syntax.return_repr
                 in
              let bind_repr =
                resugar_tscheme' "bind_repr" ed.FStar_Syntax_Syntax.bind_repr
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
  
let resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6581) ->
        let uu____6590 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____6612 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____6629 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____6636 -> false
                  | uu____6651 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
           in
        (match uu____6590 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____6683 se1 =
               match uu____6683 with
               | (datacon_ses1,tycons) ->
                   let uu____6709 = resugar_typ datacon_ses1 se1  in
                   (match uu____6709 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                in
             let uu____6724 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses
                in
             (match uu____6724 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____6759 =
                         let uu____6760 =
                           let uu____6761 =
                             let uu____6774 =
                               FStar_List.map
                                 (fun tyc  ->
                                    (tyc, FStar_Pervasives_Native.None))
                                 tycons
                                in
                             (false, uu____6774)  in
                           FStar_Parser_AST.Tycon uu____6761  in
                         decl'_to_decl se uu____6760  in
                       FStar_Pervasives_Native.Some uu____6759
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____6805,uu____6806,uu____6807,uu____6808,uu____6809)
                            ->
                            let uu____6814 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident),
                                     FStar_Pervasives_Native.None))
                               in
                            FStar_Pervasives_Native.Some uu____6814
                        | uu____6817 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____6820 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____6826) ->
        let uu____6831 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___195_6837  ->
                  match uu___195_6837 with
                  | FStar_Syntax_Syntax.Projector (uu____6838,uu____6839) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____6840 -> true
                  | uu____6841 -> false))
           in
        if uu____6831
        then FStar_Pervasives_Native.None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
               se.FStar_Syntax_Syntax.sigrng
              in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))
              in
           let t = resugar_term desugared_let  in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____6864) ->
               let uu____6877 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets))
                  in
               FStar_Pervasives_Native.Some uu____6877
           | uu____6884 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____6888,fml) ->
        let uu____6890 =
          let uu____6891 =
            let uu____6892 =
              let uu____6897 = resugar_term fml  in
              ((lid.FStar_Ident.ident), uu____6897)  in
            FStar_Parser_AST.Assume uu____6892  in
          decl'_to_decl se uu____6891  in
        FStar_Pervasives_Native.Some uu____6890
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____6899 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed
           in
        FStar_Pervasives_Native.Some uu____6899
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____6901 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed
           in
        FStar_Pervasives_Native.Some uu____6901
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source  in
        let dst = e.FStar_Syntax_Syntax.target  in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | FStar_Pervasives_Native.Some (uu____6910,t) ->
              let uu____6922 = resugar_term t  in
              FStar_Pervasives_Native.Some uu____6922
          | uu____6923 -> FStar_Pervasives_Native.None  in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | FStar_Pervasives_Native.Some (uu____6931,t) ->
              let uu____6943 = resugar_term t  in
              FStar_Pervasives_Native.Some uu____6943
          | uu____6944 -> FStar_Pervasives_Native.None  in
        let op =
          match (lift_wp, lift) with
          | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None ) ->
              FStar_Parser_AST.NonReifiableLift t
          | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some t)
              -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t) ->
              FStar_Parser_AST.LiftForFree t
          | uu____6968 -> failwith "Should not happen hopefully"  in
        let uu____6977 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               })
           in
        FStar_Pervasives_Native.Some uu____6977
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____6987 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6987 with
         | (bs1,c1) ->
             let bs2 =
               let uu____6997 = FStar_Options.print_implicits ()  in
               if uu____6997 then bs1 else filter_imp bs1  in
             let bs3 =
               FStar_All.pipe_right bs2
                 (map_opt
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng))
                in
             let uu____7006 =
               let uu____7007 =
                 let uu____7008 =
                   let uu____7021 =
                     let uu____7030 =
                       let uu____7037 =
                         let uu____7038 =
                           let uu____7051 = resugar_comp c1  in
                           ((lid.FStar_Ident.ident), bs3,
                             FStar_Pervasives_Native.None, uu____7051)
                            in
                         FStar_Parser_AST.TyconAbbrev uu____7038  in
                       (uu____7037, FStar_Pervasives_Native.None)  in
                     [uu____7030]  in
                   (false, uu____7021)  in
                 FStar_Parser_AST.Tycon uu____7008  in
               decl'_to_decl se uu____7007  in
             FStar_Pervasives_Native.Some uu____7006)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____7079 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
        FStar_Pervasives_Native.Some uu____7079
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____7083 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_7089  ->
                  match uu___196_7089 with
                  | FStar_Syntax_Syntax.Projector (uu____7090,uu____7091) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____7092 -> true
                  | uu____7093 -> false))
           in
        if uu____7083
        then FStar_Pervasives_Native.None
        else
          (let t' =
             let uu____7098 =
               (let uu____7101 = FStar_Options.print_universes ()  in
                Prims.op_Negation uu____7101) || (FStar_List.isEmpty uvs)
                in
             if uu____7098
             then resugar_term t
             else
               (let uu____7103 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                match uu____7103 with
                | (uvs1,t1) ->
                    let universes = universe_to_string uvs1  in
                    let uu____7111 = resugar_term t1  in
                    label universes uu____7111)
              in
           let uu____7112 =
             decl'_to_decl se
               (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
              in
           FStar_Pervasives_Native.Some uu____7112)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7113 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_datacon uu____7130 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Sig_main uu____7145 -> FStar_Pervasives_Native.None
  